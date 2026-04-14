import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.GeneralSyntax
import MRiscX.Elab.HandleRegister
import Lean

open Lean
open Lean Elab Term

private def numOrIdentAsTerm (s : TSyntax `num_or_ident) : TermElabM (TSyntax `term) := do
  match s with
  | `(num_or_ident| $n:num) =>
      `(term| $n:num)
  | `(num_or_ident| $i:ident) =>
      `(term| $i:ident)
  | _ =>
      throwError "unsupported num_or_ident in instruction-set hoare assignment"

private def registerIndexAsTerm (r : TSyntax `register) : TermElabM (TSyntax `term) := do
  if let some reg := getCorrespondingRegisterName? r then
    let n : TSyntax `num := Syntax.mkNumLit s!"{reg.nr}"
    `(term| $n:num)
  else
    match r with
    | `(register| x $i:num_or_ident) =>
        numOrIdentAsTerm i
    | _ =>
        throwError "unsupported register in instruction-set hoare assignment"

private def mkRegisterNameFromIdx (idx : TSyntax `term) : TermElabM (TSyntax `term) := do
  `(term| RegisterName.mk (RegisterNr.ofUInt64 $idx:term) (@toString UInt64 instToStringUInt64 $idx:term))

private partial def replaceInstrSetKeywords (stx : Term) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  go stx
where
  go : Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
      `(term| ($stateTerm:term).terminated)
  | _stx@`(⸨pc⸩) =>
      `(term| ($stateTerm:term).pc)
  | stx =>
      match stx with
      | .node _ k args => do
          let args ← args.mapM go
          return .node (.fromRef stx (canonical := true)) k args
      | _ => pure stx

private partial def getInstrSetAssignmentArray
    (stx : TSyntax `instr_set_hoare_assignment_chain)
    (curArr : Array (TSyntax `instr_set_hoare_assignment)) :
    TermElabM (Array (TSyntax `instr_set_hoare_assignment)) := do
  match stx with
  | `(instr_set_hoare_assignment_chain| $t:instr_set_hoare_assignment) =>
      return curArr.push t
  | `(instr_set_hoare_assignment_chain| $t1:instr_set_hoare_assignment ; $t2:instr_set_hoare_assignment) =>
      return (curArr.push t1).push t2
  | `(instr_set_hoare_assignment_chain| $t:instr_set_hoare_assignment ; $s:instr_set_hoare_assignment_chain) =>
      return (← getInstrSetAssignmentArray s (curArr.push t))
  | _ =>
      throwError "unknown instruction-set hoare assignment chain"

private def foldInstrSetAssignment
    (element : TSyntax `instr_set_hoare_assignment)
    (curTerm : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match element with
  | `(instr_set_hoare_assignment| x[$r:num_or_ident] ← $t:term)
  | `(instr_set_hoare_assignment| x[$r:num_or_ident] <- $t:term) => do
      let idx ← numOrIdentAsTerm r
      let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $reg $newT)
  | `(instr_set_hoare_assignment| x[$r:register] ← $t:term)
  | `(instr_set_hoare_assignment| x[$r:register] <- $t:term) => do
      let idx ← registerIndexAsTerm r
      let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $reg $newT)
  | `(instr_set_hoare_assignment| mem[$m:term] ← $t:term)
  | `(instr_set_hoare_assignment| mem[$m:term] <- $t:term) => do
      let newM : TSyntax `term := ⟨← replaceInstrSetKeywords m curTerm⟩
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addMemory ($curTerm) $newM $newT)
  | `(instr_set_hoare_assignment| pc++) =>
      `(term| MState.incInstrCounter (MState.incPc ($curTerm)))
  | `(instr_set_hoare_assignment| $pc:ident ++)
    =>
      if pc.getId == `pc then
        `(term| MState.incInstrCounter (MState.incPc ($curTerm)))
      else
        throwError "only `pc++` is supported in instruction-set hoare assignment"
  | `(instr_set_hoare_assignment| $pc:ident ← $i:term)
  | `(instr_set_hoare_assignment| $pc:ident <- $i:term) =>
      if pc.getId == `pc then
        `(term| MState.incInstrCounter (MState.setPc ($curTerm) $i:term))
      else
        throwError "only `pc <- ...` is supported in instruction-set hoare assignment"
  | _ =>
      throwError "unknown instruction-set hoare assignment element"

private def generateInstrSetAssignmentSyntax
    (hChain : TSyntax `instr_set_hoare_assignment_chain)
    (stateTerm : TSyntax `term) : TermElabM Syntax := do
  let termArray ← getInstrSetAssignmentArray hChain #[]
  let result : TSyntax `term ← termArray.foldrM foldInstrSetAssignment stateTerm
  pure result.raw

private partial def rewriteInstrSetAssignmentTerms (stx : Syntax) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  withFreshMacroScope do
    go stx
where
  go : Syntax → TermElabM Syntax
  | _stx@`(term| ⟦⟧) =>
      return stateTerm.raw
  | _stx@`(term| ⟦$h:instr_set_hoare_assignment_chain⟧) => do
      return (← generateInstrSetAssignmentSyntax h stateTerm)
  | stx =>
      match stx with
      | .node _ k args => do
          let args ← args.mapM go
          return .node (.fromRef stx (canonical := true)) k args
      | _ => pure stx

private def processInstrSetHoareTerm (stx : Term) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  let rewritten ← rewriteInstrSetAssignmentTerms stx.raw stateTerm
  replaceInstrSetKeywords ⟨rewritten⟩ stateTerm

private partial def elabInstrSetHoareTerm (stx : Term) : TermElabM Term := do
  let stId : TSyntax `ident := mkIdent `st
  let stTerm : TSyntax `term ← `(term| $stId:ident)
  let newStx ← processInstrSetHoareTerm stx stTerm
  return (← `(term| fun $stId:ident => ($(⟨newStx⟩))))

elab "⧼" t:term "⧽" : term => do
  let newT ← elabInstrSetHoareTerm t
  return (← Lean.Elab.Term.elabTerm (← `(term| $newT:term)) none)

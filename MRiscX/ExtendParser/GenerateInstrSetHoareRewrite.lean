import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.GeneralSyntax
import MRiscX.Elab.HandleRegister
import MRiscX.Elab.HandleNumOrIdent
import Lean

open Lean
open Lean Meta
open Lean Elab Term

private def registerNrOfBareName? (s : String) : Option Nat :=
  match s with
  | "x0" => some 0
  | "x1" => some 1
  | "x2" => some 2
  | "x3" => some 3
  | "x4" => some 4
  | "x5" => some 5
  | "x6" => some 6
  | "x7" => some 7
  | "x8" => some 8
  | "x9" => some 9
  | "x10" => some 10
  | "x11" => some 11
  | "x12" => some 12
  | "x13" => some 13
  | "x14" => some 14
  | "x15" => some 15
  | "x16" => some 16
  | "x17" => some 17
  | "x18" => some 18
  | "x19" => some 19
  | "x20" => some 20
  | "x21" => some 21
  | "x22" => some 22
  | "x23" => some 23
  | "x24" => some 24
  | "x25" => some 25
  | "x26" => some 26
  | "x27" => some 27
  | "x28" => some 28
  | "x29" => some 29
  | "x30" => some 30
  | "x31" => some 31
  | _ => none

private def registerNrOfAbiName? (s : String) : Option Nat :=
  match s with
  | "zero" => some 0
  | "ra" => some 1
  | "sp" => some 2
  | "gp" => some 3
  | "tp" => some 4
  | "t0" => some 5
  | "t1" => some 6
  | "t2" => some 7
  | "s0" => some 8
  | "fp" => some 8
  | "s1" => some 9
  | "a0" => some 10
  | "a1" => some 11
  | "a2" => some 12
  | "a3" => some 13
  | "a4" => some 14
  | "a5" => some 15
  | "a6" => some 16
  | "a7" => some 17
  | "s2" => some 18
  | "s3" => some 19
  | "s4" => some 20
  | "s5" => some 21
  | "s6" => some 22
  | "s7" => some 23
  | "s8" => some 24
  | "s9" => some 25
  | "s10" => some 26
  | "s11" => some 27
  | "t3" => some 28
  | "t4" => some 29
  | "t5" => some 30
  | "t6" => some 31
  | _ => none

private def registerNrOfName? (s : String) : Option Nat :=
  match registerNrOfBareName? s with
  | some n => some n
  | none => registerNrOfAbiName? s

private def numOrIdentAsTerm (s : TSyntax `num_or_ident) : TermElabM (TSyntax `term) := do
  match s with
  | `(num_or_ident| $n:num) =>
      `(term| $n:num)
  | `(num_or_ident| $i:ident) => do
      match registerNrOfName? i.getId.eraseMacroScopes.toString with
      | some n =>
          let idx : TSyntax `num := Syntax.mkNumLit s!"{n}"
          `(term| $idx:num)
      | none =>
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

private def numOrIdentAsRegisterTerm (s : TSyntax `num_or_ident) : TermElabM (TSyntax `term) := do
  match s with
  | `(num_or_ident| $n:num) =>
      let idx : TSyntax `term ← `(term| $n:num)
      mkRegisterNameFromIdx idx
  | `(num_or_ident| $i:ident) => do
      if let some decl := (← getLCtx).findFromUserName? i.getId then
        if ← isDefEq decl.type (mkConst ``RegisterName) then
          `(term| $i:ident)
        else
          let idx : TSyntax `term ← `(term| $i:ident)
          mkRegisterNameFromIdx idx
      else
        match registerNrOfName? i.getId.eraseMacroScopes.toString with
        | some n =>
            let idx : TSyntax `term ← `(term| $(Syntax.mkNumLit s!"{n}"):num)
            mkRegisterNameFromIdx idx
        | none =>
            let idx : TSyntax `term ← `(term| $i:ident)
            mkRegisterNameFromIdx idx
  | _ =>
      throwError "unsupported num_or_ident in instruction-set hoare term"

private partial def replaceInstrSetKeywords (stx : Term) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  go stx
where
  go : Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
      `(term| ($stateTerm:term).terminated)
  | _stx@`(⸨pc⸩) =>
      `(term| ($stateTerm:term).pc)
  | _stx@`(x[$r:register]) => do
      let idx ← registerIndexAsTerm r
      let reg ← mkRegisterNameFromIdx idx
      `(term| MState.getRegisterAt ($stateTerm:term) $reg)
  | _stx@`(x[$r:num_or_ident]) => do
      let reg ← numOrIdentAsRegisterTerm r
      `(term| MState.getRegisterAt ($stateTerm:term) $reg)
  | _stx@`(mem[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.getMemoryAt) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_ub[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadByte_unsigned) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_sb[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadByte_signed) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_uh[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadHalfword_unsigned) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_sh[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadHalfword_signed) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_uw[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadWord_unsigned) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_sw[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadWord_signed) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(mem_d[$t:term]) => do
      let et ← replaceInstrSetKeywords t stateTerm
      return ←`(term | $(mkIdent `MState.loadDouble) ($stateTerm) ($(⟨et⟩)))
  | _stx@`(labels[$s:ident]) => do
      let lblTerm ← checkIfVariableToTerm s false
      `(term| MState.getLabelAt ($stateTerm:term) $lblTerm:term)
  | _stx@`(labels[.$s:ident]) => do
      let lblTerm ← checkIfVariableToTerm s true
      `(term| MState.getLabelAt ($stateTerm:term) $lblTerm:term)
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
      -- let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $idx $newT)
  | `(instr_set_hoare_assignment| x[$r:register] ← $t:term)
  | `(instr_set_hoare_assignment| x[$r:register] <- $t:term) => do
      let idx ← registerIndexAsTerm r
      -- let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $idx $newT)
  | `(instr_set_hoare_assignment| mem[$m:term] ← $t:term)
  | `(instr_set_hoare_assignment| mem[$m:term] <- $t:term) => do
      let newM : TSyntax `term := ⟨← replaceInstrSetKeywords m curTerm⟩
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addMemory ($curTerm) $newM $newT)
  | `(instr_set_hoare_assignment| pc++) =>
      `(term| (MState.incPc ($curTerm)))
  | `(instr_set_hoare_assignment| $pc:ident ++)
    =>
      if pc.getId == `pc then
        `(term| (MState.incPc ($curTerm)))
      else
        throwError "only `pc++` is supported in instruction-set hoare assignment"
  | `(instr_set_hoare_assignment| $pc:ident ← $i:term)
  | `(instr_set_hoare_assignment| $pc:ident <- $i:term) =>
      if pc.getId == `pc then
        `(term| (MState.setPc ($curTerm) $i:term))
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

elab (name := elabInstrSetAssertionTerm) "⦃" t:term "⦄" : term => do
  Lean.Elab.Term.elabTerm (← `(term| ⧼$t:term⧽)) none

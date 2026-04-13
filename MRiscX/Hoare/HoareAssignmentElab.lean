import Lean
-- import MRiscX.Elab.HandleNumOrIdent
-- import MRiscX.Elab.HandleRegister
import MRiscX.Parser.HoareSyntax
import MRiscX.Elab.HandleNumOrIdent
import MRiscX.Elab.HandleRegister
import MRiscX.Hoare.HoareCore
open Lean Elab

/-
This file contains the elaboaration of the hoare assignment terms.
Essentially, there are two types of hoare terms.
The "regular" hoare term, which represents the terms within a hoare triple.
E.g. ⦃x[2] = 12 ∧ ¬⸨termnated⸩⦄
These hoare terms just have to be translated to the function calls.

Then there is the HoareAssignment is represented by the ⟦⟧ brackets. They mean the following:

There is an Assertion which is true under the condition, that
the term inside the ⟦⟧ brackets is fulfilled
Those terms are slightly different than the "regular" hoare terms, because the
meaning is not the same. E.g. we don't want to write something like
```
x[r] = v
```
because this could indicate that if the statement is true before the hoare triple acutally
begins, the Assertion is true afterwards as well.
But we want to imply, that this Assertion is just true, when this happens during this
hoare triple.
So instead, we introduce the syntax of
```
x[r] ← v
```
to underline the fact, that the register r is passed the value wihtin this hoare triple.
To archieve this, a certain state has to be passed in as well to indicate, on which state
the functioncalls should be made.
These HoareAssignments are used for the specification of the instruction.
-/

-- def adsf {α InstrType CodeType RegisterNrType RegisterValType PcType}
--     [MachineStateI α InstrType CodeType RegisterNrType RegisterValType PcType]
--     (a : α)  :=
--   (MachineStateI.getPc InstrType CodeType RegisterNrType RegisterValType a)

-- def adsf' {α InstrType CodeType RegisterNrType RegisterValType PcType}
--     [MachineStateI α InstrType CodeType RegisterNrType RegisterValType PcType]
--     (a : α) (b : RegisterNrType) :=
--   @MachineStateI.getRegisterAt α InstrType CodeType RegisterNrType RegisterValType PcType _ a b

  /-
This function is similar to expandCDot?.
It traverses the given syntax and searches for patterns to replace the keywords
defined as syntax terminals with the actual functions calls
-/
partial def replaceKeywords (stx : Term) (curState : TSyntax `term) : TermElabM Syntax := do
  go stx
where
  /--
  Auxiliary function for expanding the `x[num]`, `mem[num]` and
  `mem[x[num]]` notation.
  If `stx` is a `x[num]`, `mem[num]` or `mem[x[num]]`,
  we return the corresponding functions on the state.
  Otherwise, we just return `stx`.
  -/
  go : Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
    return ←`(term | $(mkIdent `MachineStateI.getTerminated)  $(mkIdent `InstrType)
                                                              $(mkIdent `CodeType)
                                                              $(mkIdent `RegisterNrType)
                                                              $(mkIdent `RegisterValType)
                                                              $(mkIdent `PcType)
                                                              ($curState))
  | _stx@`(x[$r:register]) => do
    match r with
    | `(register | $a:register_bare)
    | `(register | $a:register_abi) =>
      let some nr := getCorrespondingRegisterName? ⟨a⟩
                  | throwError s!"Could not get a valid RegisterNr from {a}"

      let t : TSyntax `term := Syntax.mkNumLit s!"{nr.nr}"
      return ←`(term | $(mkIdent `MachineStateI.getRegisterAt)  $(mkIdent `InstrType)
                                                              $(mkIdent `CodeType)
                                                              -- $(mkIdent `RegisterNrType)
                                                              -- $(mkIdent `RegisterValType)
                                                              $(mkIdent `PcType)
                                                              ($curState)
                                                              ($(mkIdent `RegisterName.mk)
                                                              ($(mkIdent `RegisterNr.ofUInt64) $t)
                                                              $(Syntax.mkStrLit nr.name)))
    | `(register | x $i:num_or_ident) =>

      let newR ← parseMriscxNumOrIdentToTerm i
      match newR with
      | `(term | $n:num) =>
        let name := s!"{n.getNat}"
        return ←`(term | $(mkIdent `MachineStateI.getRegisterAt)  $(mkIdent `InstrType)
                                                                  $(mkIdent `CodeType)
                                                                  -- $(mkIdent `RegisterNrType)
                                                                  -- $(mkIdent `RegisterValType)
                                                                  $(mkIdent `PcType)
                                                                  ($curState)
                                                                  ($(mkIdent `RegisterName.mk)
                                                                  ($(mkIdent `RegisterNr.ofUInt64) $newR)
                                                                  $(Syntax.mkStrLit name)))
      | `(term | $i:ident) =>
        let name := i.getId.getString!
        return ←`(term | $(mkIdent `MachineStateI.getRegisterAt)  $(mkIdent `InstrType)
                                                                  $(mkIdent `CodeType)
                                                                  -- $(mkIdent `RegisterNrType)
                                                                  -- $(mkIdent `RegisterValType)
                                                                  $(mkIdent `PcType)
                                                                  ($curState)
                                                                  ($(mkIdent `RegisterName.mk)
                                                                  ($(mkIdent `RegisterNr.ofUInt64) $newR)
                                                                  $(Syntax.mkStrLit name)))
      | _ => throwError "fail1"
    | _ => throwError "fail2"
  | _stx@`(mem[$t:term]) => do
    let et ← replaceKeywords t curState
    return ←`(term | $(mkIdent `MState.getMemoryAt) ($curState) ($(⟨et⟩)))
  | _stx@`(labels[$s:ident]) => do
    let newS ← checkIfVariableToTerm s false
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(labels[.$s:ident]) => do
    let newS ← checkIfVariableToTerm s true
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(⸨pc⸩) => do
    return ←`(term | $(mkIdent `MachineStateI.getPc)  $(mkIdent `InstrType)
                                                      $(mkIdent `CodeType)
                                                      $(mkIdent `RegisterNrType)
                                                      $(mkIdent `RegisterValType)
                                                      -- $(mkIdent `PcType)
                                                      ($curState))
  | stx => match stx with
    | .node _ k args => do
      let args ← args.mapM go
      return .node (.fromRef stx (canonical := true)) k args
    | _ => pure stx

/-
Seperate all the assignemnts within the ⟦⟧ and store in one array
-/
partial def getHoareAssignmentArray (stx: TSyntax `hoare_assignment_chain)
    (curArr: Array (TSyntax `hoare_assignment)): TermElabM (Array (TSyntax `hoare_assignment)) := do
  match stx with
  | `(hoare_assignment_chain | $t:hoare_assignment) =>
    return curArr.push t
  | `(hoare_assignment_chain | $t1:hoare_assignment ; $t2:hoare_assignment) =>
    return (curArr.push t1).push t2
  | `(hoare_assignment_chain | $t:hoare_assignment ; $s:hoare_assignment_chain) =>
    return ←(getHoareAssignmentArray s (curArr.push t))
  | _ => throwError s!"hoare assignment {stx} term not known!"

-- def mkRegisterNameTermFromNumOrIdent (i : TSyntax `num_or_ident) :=


/-
Parse the TSyntax to the actual function calls
-/

def foldTermArray (element: TSyntax `hoare_assignment) (curTerm: TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match element with
  | `(hoare_assignment | x[$r:num_or_ident] ← $t:term)
  | `(hoare_assignment | x[$r:num_or_ident] <- $t:term) => do
    let valOfNewR ← parseMriscxNumOrIdentToTerm r
    let name ← `(@toString $(mkIdent `UInt64) $(mkIdent `instToStringUInt64) $valOfNewR)

    let newR ← `($(mkIdent `RegisterName.mk) ($(mkIdent `RegisterNr.ofUInt64) $valOfNewR) $name)
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addRegister) ($curTerm) $newR $newT)
  -- | `(hoare_assignment | x[$r:mriscx_registers] ← $t:term)
  -- | `(hoare_assignment | x[$r:mriscx_registers] <- $t:term) => do
  --   let valOfNewR ← parseMriscxNumOrIdentToTerm r
  --   let name := Syntax.mkStrLit s!"x{valOfNewR}"
  --   let newR ← `($(mkIdent `RegisterName.mk) ($(mkIdent `RegisterNr.ofUInt64) $name))
  --   let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    -- return ←`(term | $(mkIdent `MState.addRegister) ($curTerm) $newR $newT)
  | `(hoare_assignment | mem[$m:term] ← $t:term)
  | `(hoare_assignment | mem[$m:term] <- $t:term) => do
    let newM := ⟨←replaceKeywords m curTerm⟩
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addMemory) ($curTerm) $newM $newT)
  | `(hoare_assignment | pc++) =>
    return ←`(term | $(mkIdent `MState.incInstrCounter) ($(mkIdent `MState.incPc) ($curTerm)))
  | `(hoare_assignment | pc ← $i:term) => do
    return ←`(term | $(mkIdent `MState.incInstrCounter) ($(mkIdent `MState.setPc) ($curTerm) $i))
  | _ => throwError s!"{element}"

/-
Construct the final lambda term
-/
partial def generateHoareAssignmentSyntax (stx: TSyntax `hoare_assignment_chain): TermElabM (Syntax)
    := do
  let termArray ← getHoareAssignmentArray stx #[]
  let result ← termArray.foldrM foldTermArray (←`($(mkIdent `st)))
  return result

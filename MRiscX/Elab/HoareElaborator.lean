import MRiscX.Hoare.HoareCore
import MRiscX.Elab.CodeElaborator
import MRiscX.Parser.HoareSyntax


open Lean Elab

/-
This file contains the definition of the Hoare Notation and elaboration.
The Syntax of the hoare triples is as close as possible to the notation from
the paper of lundberg et al.. Some exceptions had to be made since "[]" are already
widely known as lists.
-/
partial def processHoareTerm (stx : Term) : TermElabM Syntax := do
  withFreshMacroScope do
    let mut newStx ← (go stx)
    return newStx
where
  /-
    Differntiate between hoare assignment and usual term in pre and post condition.
  -/
  go : Syntax → TermElabM Syntax
  | _stx@`(hoare_assignment_term | ⟦$h:hoare_assignment_chain⟧) => do
    return ←generateHoareAssignmentSyntax h
  | _stx@`($t:term) => do
    let mut newStx ← replaceKeywords t (←`($(mkIdent `st)))
    return newStx



partial def elabHoareTerm (stx : Term) : TermElabM (Term) := do
  let newStx ← processHoareTerm stx
  let stIdent := mkIdent `st
  return ←`(fun $stIdent : MState => ($(⟨newStx⟩)))


elab "⦃" t:term "⦄" : term => do
  let newTOpt ← elabHoareTerm t
  return ← Lean.Elab.Term.elabTerm (←`($newTOpt)) (some (.const ``String []))


def mriscxSyntaxToTerm (stx : Array (TSyntax `mriscx_label)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) := ←`(mriscx
                                      $stx*
                                     end)
  return newStx

def mriscxSpecToTerm (stx: (TSyntax  `mriscx_Instr)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) ←`(⟪$stx⟫)
  return ←`($newStx)



elab "hoare" syn:mriscx_spec linebreak
      "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
      "end" : term => do
  let translatedP ← elabHoareTerm P
  let translatedQ ← elabHoareTerm Q
  match syn with
  | `(mriscx_spec | ⟪$i:mriscx_Instr⟫) => do
    let synAsTerm ← mriscxSpecToTerm i
    return ←Lean.Elab.Term.elabTerm
        (←`($(mkIdent ``hoare_triple_up_1) $translatedP $translatedQ $l $L_w $L_b $synAsTerm))
        (some (.const ``String []))
  | _ => throwError "Expected syntax of type mriscx_spec with ⟪⟫ braces!"



elab t:hoare_term : term => do
  match t with
  | `(hoare_term | $syn:mriscx_syntax
    ⦃ $P:term ⦄ $l:term ↦ ⟨ $L_w:term | $L_b:term ⟩ ⦃ $Q:term ⦄) =>
    let translatedP ← elabHoareTerm P
    let translatedQ ← elabHoareTerm Q
    let labels ← getLabelMapFromSyntax syn
    let evaluatedLw := ⟨(←replaceLabels L_w labels)⟩
    let evaluatedLb := ⟨(←replaceLabels L_b labels)⟩
    let evaluatedL := ⟨(←replaceLabels l labels)⟩

    match syn with
    | `(mriscx_syntax | mriscx
      $labelsSyn:mriscx_label*
      end) => do
      let mriscxSyntaxAsTerm ← mriscxSyntaxToTerm labelsSyn
      return ←Lean.Elab.Term.elabTerm (←`($(mkIdent ``hoare_triple_up) $translatedP $translatedQ
        $evaluatedL $evaluatedLw $evaluatedLb $mriscxSyntaxAsTerm))
        (some (.const ``String []))
    | _ => throwError "expected mriscx syntax while elaborating hoare term"
  | _ => throwError "failure"


elab id:ident withPosition(linebreak ppDedent(ppLine))
  "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
   : term => do
  let translatedP ← elabHoareTerm P
  let translatedQ ← elabHoareTerm Q
  let evaluatedLw := ⟨(←replaceLabelsWithIdent L_w id)⟩
  let evaluatedLb := ⟨(←replaceLabelsWithIdent L_b id)⟩
  let evaluatedL := ⟨(←replaceLabelsWithIdent l id)⟩

  return ←Lean.Elab.Term.elabTerm
      (←`($(mkIdent ``hoare_triple_up) $translatedP $translatedQ $evaluatedL $evaluatedLw
          $evaluatedLb $id))
      (some (.const ``String []))

-- Fallback elab if no Labelnames in l, L_w or L_b required
elab id:ident
    "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
    : term => do
  return ←Lean.Elab.Term.elabTerm
    (←`($(mkIdent ``hoare_triple_up) $P $Q $l $L_w $L_b $id))
    (some (.const ``String []))


-- Elab of hoare assignment
elab "⟦"stx:hoare_assignment_chain"⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← generateHoareAssignmentSyntax stx) none

elab "⟦⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← `($(mkIdent `st))) none

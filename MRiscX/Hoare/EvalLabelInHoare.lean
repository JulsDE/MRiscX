import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Elab.HandleExpr
open Lean Elab

/-
This file contains a logic to replace the labelname with the actual pc index
within a hoare triple
-/

partial def replaceLabels (stx : Term) (labels : LabelMap) : TermElabM Syntax := do
  withFreshMacroScope do
    let (newStx, _) ← (go stx).run labels
    return newStx
where
  /-
  Auxiliary function for expanding the `labels[ident]`.

  Otherwise, we just return `stx`.
  -/
  go : Syntax → StateT (LabelMap) TermElabM Syntax
  | _stx@`($s:str) => do
    let str := s.getString
    let mapEntryAtStr := (←get).get str
    match mapEntryAtStr with
    | some i => do
      return Syntax.mkNumLit (toString i)
    | none => throwError s!"No label found with name {str}"
  | stx => match stx with
    | .node _ k args => do
      let args ← args.mapM go
      return .node (.fromRef stx (canonical := true)) k args
    | _ => pure stx


partial def replaceLabelsWithIdent (stx : Term) (i : Ident) : TermElabM Syntax := do
  let e ← Term.elabTerm i none
  if e.isFVar then
    return stx
  let labels ← getLabelMapExpr e
  return ←replaceLabels stx labels

import Lean
open Lean Meta

def findHypTypeM? (ctx : LocalContext) (n : Name) : MetaM (Option Expr) :=
  ctx.findDeclM? (fun decl =>
    if decl.userName == n then
      return some decl.type
    else
      return none)

def findHypTypeM (ctx : LocalContext) (n : Name): MetaM (Expr) := do
  let some res ← (findHypTypeM? ctx n)
      | throwError s!"Could not find {n} in hypothesis"
  return res

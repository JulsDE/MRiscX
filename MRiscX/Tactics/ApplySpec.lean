import Lean
import MRiscX.AbstractSyntax.Instr
import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Elab.HandleNumOrIdent
import MRiscX.Elab.HandleExpr
import Mathlib.Data.Set.Basic
import MRiscX.Basic

open Lean Meta Elab Parser Tactic

/--
tactic to automate application of specification to get rid of the need of providing
values like `l`, `r` etc.
-/
elab "apply_spec" + t:term : tactic => do
  -- TODO
  let originalGoal ← getMainGoal
  let oGoalType ← originalGoal.getType
  let L_w_expr := oGoalType.getArg! 3
  let L_b_expr  := oGoalType.getArg! 4

  logInfo s!"{L_b_expr}"
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let f ← Meta.whnf <| ←goal.getType
  evalTactic (←`(tactic | simp))


/--
tactic to automate application of specification to get rid of the need of providing
the name of the specification itself
-/
elab "auto_apply_spec": tactic => do
  -- TODO
  evalTactic (←`(tactic | simp))


example:
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end
    -- Assert assignment of register as precondition
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by

  sorry

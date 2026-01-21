import Lean
import Mathlib.Tactic.Push
import Mathlib.Data.Set.Basic

open Lean Elab Tactic Meta

/-
This file contains some custom tactics which are used several times wihthin all over
this project.
-/

elab "simp_set_eq" : tactic => do
  evalTactic (← `(tactic | try (ext; simp; grind)))


elab "apply_to_last_goal" t:tacticSeq : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    match goals.getLast? with
    | some goal =>
      Lean.Elab.Tactic.setGoals ([goal] ++ goals.extract 0 (goals.length - 1))

    | none => throwError "No goals found while trying to apply {t} to the last goal"

  evalTactic (← `(tactic | . $t ))

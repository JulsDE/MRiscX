import Lean

import Lean.Elab.Tactic
import MRiscX.AbstractSyntax.Map
import MRiscX.Semantics.MsTheory
import MRiscX.Util.BasicTheorems
import MRiscX.Tactics.SplitLastSeq

open Lean Meta Elab Parser Tactic RCases

/-
This file contains some custom tactics for proof automation.
Essentially, there are tactics used in proving the fulfilment of the
specification and there are tactics to use while proving a
piece of code.
It is planned to extend this file to a level, where users can
prove a program written in risc-v without the requirement to know lean tactics at all,
but just use the tactics defined in this file.
-/



/- Tries to solve a `s.currInstr = instr` goal. Requires the s.cdoe and s.pc being introduced
as `h_code'` and `h_pc` respectively as hypothesis -/
elab "simp_currInstr" : tactic => do
  evalTactic (← `(tactic| simp))
  evalTactic (← `(tactic| rw [($(mkIdent `h_code')), ($(mkIdent `h_pc))]))
  evalTactic (← `(tactic| simp [t_update_neq, t_update_eq]))

/- Tries to solve goals where `(pmap).get r = some label`.-/
elab "simp_t_update" : tactic => do
  evalTactic (← `( tactic | repeat (first | rw [t_update_eq] | rw [t_update_neq]
                            <;> try (apply Ne.symm; try assumption))
                            <;> try assumption))
  evalTactic (← `(tactic | repeat first
                          | constructor
                          | assumption))

/- A small tactic to prove `∀ (n' : ℕ), 0 < n' → ¬n' = 0`-/
macro "zero_lt_ne_zero" : tactic =>
  `(tactic | try (intros n' h ; intro h_eq ; rw [h_eq] at h); simp at h)

/- The proof for most specifications of instructions -/
elab "hoare_simp_specification" : tactic => do
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| exists s.runOneStep))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
      intros _
      exists 1
      apply And.intro
      simp
      case right =>
        simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
        unfold $(mkIdent `MState.runOneStep)
        rw [h_terminated, ←h_pc, HCurr]
        simp
        zero_lt_ne_zero
  ))
  evalTactic (← `(tactic|
    case right =>
      -- try rw [xor_iff_notation] at pre
      simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep)
      rw [HCurr]
      simp
      simp [pre, h_terminated, ←h_pc]
      simp at pre
      rw [h_terminated] at pre
      rw [h_pc]
      rw [h_pc] at pre
      exact pre
  ))


/- The proof of correctness for the specification of conditional jump instruction when the condition
is false -/
elab "simp_jump_spec_false" : tactic => do
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| simp at h_cond))
  evalTactic (← `(tactic| simp at h_curr))
  evalTactic (← `(tactic| exists state.runOneStep))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
      intros _
      exists 1
      apply And.intro; simp
      . repeat (constructor <;> try simp)
        . simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
          unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
            $(mkIdent `MState.jump)
          rw [h_terminated, ← h_pc]
          simp [h_curr, h_cond]
        . zero_lt_ne_zero
  ))
  evalTactic (← `(tactic|
    case right =>
      simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
        $(mkIdent `MState.jump)
      rw [h_terminated]
      simp [h_curr, h_cond, pre]
      rw [← h_pc, h_terminated]
      simp
      simp [←h_pc, h_terminated] at pre
      exact pre
    ))



/- The proof of correctness for the specification of conditional jump instruction when the condition
is true -/
elab "simp_jump_spec_true" : tactic => do
  evalTactic (← `(tactic| unfold $(mkIdent `hoare_triple_up_1)))
  evalTactic (← `(tactic| rintro _ _ state h_curr h_pc ⟨pre, h_label, h_cond, h_terminated⟩))
  evalTactic (← `(tactic| simp at h_terminated))
  evalTactic (← `(tactic| simp at h_label))
  evalTactic (← `(tactic| simp at h_cond))
  evalTactic (← `(tactic| unfold MState.currInstruction at h_curr))
  evalTactic (← `(tactic| exists state.runOneStep))
  evalTactic (← `(tactic| unfold $(mkIdent `weak)))
  evalTactic (← `(tactic| apply And.intro))
  evalTactic (← `(tactic|
    case left =>
    intros _
    exists 1
    apply And.intro; simp
    . repeat (constructor <;> try simp)
      . simp [← $(mkIdent `MState.run_one_step_eq_run_n_1)]
        unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
          $(mkIdent `MState.jump)
        rw [h_terminated]
        simp [h_curr, h_label, h_cond]
      . zero_lt_ne_zero
  ))
  evalTactic (← `(tactic|
    case right =>
      simp [<- $(mkIdent `MState.run_one_step_eq_run_n_1)]
      unfold $(mkIdent `MState.runOneStep) $(mkIdent `MState.jif') $(mkIdent `MState.jif)
        $(mkIdent `MState.jump)
      unfold $(mkIdent `MState.setPc) at pre
      rw [h_terminated]
      rw [h_terminated] at pre
      simp [h_curr, h_label, h_cond, pre]
    ))



elab "simp_jump_spec" : tactic => do
  evalTactic (← `(tactic | first
                          | simp_jump_spec_false
                          | simp_jump_spec_true)
  )



/-
%%%%%%
-/

/-
Proof automation for hoare-triples
-/
/- apply S_SEQ to peel off the last instruction -/
elab &"auto" &"seq" : tactic => do
  evalTactic (← `(tactic | peel_last_instr <;> try assumption))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | apply_to_last_goal simp_set_eq))

/- apply S_SEQ' with an automatic `try assumption` on every goal that is generated -/
macro "sapply_s_seq" P:term ", " R:term ", " L_w:term ", " L_w':term : tactic => do
  `(tactic | apply $(mkIdent `S_SEQ') (P := $P) (R := $R)
    (L_w := $L_w) (L_w' := $L_w') <;> try assumption)

/- apply S_SEQ with an automatic `try assumption` on every goal that is generated -/
macro "sapply_s_seq'" P:term ", " R:term ", " L_w:term ", " L_w':term : tactic => do
  `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R)
    (L_w := $L_w) (L_w' := $L_w') <;> try assumption)


/- apply S_SEQ without the requirement to provide P and simp some trivial goals that are generated-/
elab "sapply_s_seq''" R:term &", " L_w:term &", " L_w':term &", "
    L_b:term &", " L_b':term : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := _) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))

-- TODO make this more robust
/- apply S_SEQ without providing P but explicitly provide the names of the parameters.
This is mostly for visual effects. -/
elab "sapply_s_seq''"
                      -- &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := _) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))


/- apply S_SEQ with P and explicitly provide the names of the parameters.
This is mostly for visual effects. -/
  elab "sapply_s_seq''"
                      &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))



elab "sapply_s_seq_plain"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))


elab "sapply_s_seq_plain"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapply_s_seq_plain P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))


-- TODO make this more robust
/- apply S_SEQ with P and explicitly provide the names of the parameters.
Also, apply simp_set_eq to the last goal to further automate the proving process
and to avoid having to prove the set equality. -/
elab "sapply_s_seq'''"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | . simp ))
  evalTactic (← `(tactic | apply_to_last_goal simp_set_eq ))

/- apply S_SEQ without providing P and explicitly provide the names of the parameters.
Also, apply simp_set_eq to the last goal to further automate the proving process
and to avoid having to prove the set equality. -/
elab "sapply_s_seq'''"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapply_s_seq''' P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))

/- This tactic prpares the second proofgoal after applying S_SEQ. It introduces the
parameters and unfolds `hoare_triple_up`-/
elab "prepare_second_seq": tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `l') $(mkIdent `h_l') ))
  evalTactic (← `(tactic | rw [($(mkIdent `h_l'))] ))
  evalTactic (← `(tactic | unfold hoare_triple_up))
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s) $(mkIdent `h_code') $(mkIdent `h_pc) ))
  evalTactic (← `(tactic | rw [←($(mkIdent `h_code'))] ))


/- apply specification and simp some trivial goals. Requires a hypothesis being
   introduced as `h_pc` -/
elab "apply_spec_basic" spec:term : tactic => do
  evalTactic (← `(tactic | apply $spec ))
  evalTactic (← `(tactic | simp ))
  evalTactic (← `(tactic | simp ))
  evalTactic (← `(tactic | simp_currInstr ))
  evalTactic (← `(tactic | exact $(mkIdent `h_pc) ))


/- apply specification after all hypothesis are introduced. Solve some trivial goals afterwards -/
elab "apply_spec_when_ready" spec:term : tactic => do
  evalTactic (← `(tactic | apply_spec_basic $spec ))
  evalTactic (← `(tactic | simp at *))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try simp [t_update_neq, t_update_eq]))




/- To be able to split conjunction and disjunction in hypothesis, the next two functions are
required. Those functions are from Lean.Elab.Tactic.RCases -/
def RCasesPatt.alts' (ref : Syntax) : List/-Σ-/ RCasesPatt →RCasesPatt
  | [p] => p
  | ps  => RCasesPatt.alts ref ps

/-- Parses a `Syntax` into the `RCasesPatt` type used by the `RCases` tactic. -/
partial def RCasesPatt.parse (stx : Syntax) : MetaM RCasesPatt :=
  match stx with
  | `(rcasesPatMed| $ps:rcasesPat|*) =>
    return RCasesPatt.alts' stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPatLo| $pat:rcasesPatMed : $t:term) => return .typed stx (← parse pat) t
  | `(rcasesPatLo| $pat:rcasesPatMed) => parse pat
  | `(rcasesPat| _) => return .one stx `_
  | `(rcasesPat| $h:ident) => return .one h h.getId
  | `(rcasesPat| -) => return .clear stx
  | `(rcasesPat| @$pat) => return .explicit stx (← parse pat)
  | `(rcasesPat| ⟨$ps,*⟩) => return .tuple stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPat| ($pat)) => return .paren stx (← parse pat)
  | _ => throwUnsupportedSyntax


/- a tactic which puts conjunction and disjunction in a precondition into its parts. -/
elab "split_condis" &" in " h:ident : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      if decl.userName == h.getId then
        let type := decl.type
        let pat ← splitConjDisj type
        let pat' ← RCasesPatt.parse pat
        return some pat'
      return none
    match option_matching_expr with
    | some e =>
      let tgts : Array (Option Ident × Syntax) := #[(none, h)]
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.rcases tgts e g)
    | none =>
      Lean.Meta.throwTacticEx `split_condis goal
        (m!"failure")

-- TODO unfold any identifier
/- apply specification for the 'first goal' of S_SEQ. This is only possible, when the goal has
been modified to a point where the first goal of S_SEQ is only one execution step -/
elab "apply_spec_default" spec:term : tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s) $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | rw [← $(mkIdent `h_code')] ))
  evalTactic (← `(tactic | split_condis in $(mkIdent `user_precondition) ))
  evalTactic (← `(tactic | repeat (apply_spec_when_ready $spec)))

/- apply specification for the 'second goal' of S_SEQ.-/
elab "apply_spec_for_second" spec:term : tactic => do
  evalTactic (← `(tactic | prepare_second_seq))
  evalTactic (← `(tactic | intros $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | split_condis in $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | apply_spec_when_ready $spec ))
  evalTactic (← `(tactic | try repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try repeat (simp [t_update_neq, t_update_eq])))


/- apply specification on any goal after applying S_SEQ -/
elab "apply_spec" spec:term : tactic => do
  evalTactic (← `(tactic | first
                          | apply_spec_default $spec
                          | apply_spec_for_second $spec))
  evalTactic (← `(tactic | try simp_t_update))

import MRiscX.Hoare.HoareTheory
import MRiscX.Delab.DelabHoare
import Mathlib.Data.Set.BooleanAlgebra

/-
This file contains the hoare rules from the paper of lundberg et al.
Those rules are being defined and proved.
By proving these rules, we archive
1. showing the correctness of the rules themselves
2. verifying the compatibility of the constructed machine model and the hoare
  logic from lundberg et al.


The assumptions of Hoare's rules used here differ in some respects from those in lundberg et al.
This is because conditions such as $L_W \cap L_B = \emptyset$ are preconditions from
the judgement of \mathcal{L}_{AS}.
These statements must be valid in order for the conditions for applying the assumptions to be met.

TODO: prove of S_LOOP
-/

/--
Allows to weaken the Hoare triple by removing a set
$`L` from $`L_B`
-/
theorem BL_SUBSET: ∀ (code : Code) (P Q : Assertion) (l: UInt64) (L_w L_b L : Set UInt64),
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b \ L⟩⦃Q⦄
:= by
  intros c P Q l L_w L_b L T
  unfold hoare_triple_up
  intros H _ h_LwEmpty s HCode pre HPc
  have L_b_sub : L_b \ L ⊆ L_b := by
    apply Set.diff_subset
  specialize H T h_LwEmpty s HCode pre HPc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  constructor
  · apply weak_with_less_BL_weakens ; exact H1
  · constructor
    · exact H2
    · apply Set.notMem_subset
      · exact L_b_sub
      · exact H3

/--
Allows to weaken the Hoare triple
by moving a set $`L` it to $`L_W` without restrictions.
-/
theorem BL_TO_WL: ∀ (code : Code) (P Q : Assertion) (l : UInt64) (L_w L_b L : Set UInt64),
  L ⊆ L_b →
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  L_w ≠ ∅ →
  code
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  code
  ⦃P⦄ l ↦ ⟨L_w ∪ L | L_b \ L⟩⦃Q⦄
  := by
  intros c P Q l L_w L_b L TSub TInter TEmpty
  unfold hoare_triple_up
  intros H _ _ s HCode pre HPc
  specialize H  TInter TEmpty s HCode pre HPc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  unfold weak
  constructor
  · apply weak_L_w_with_L_from_L_b <;> try assumption
  . constructor <;> try assumption
    apply Set.notMem_subset (t := L_b) <;> try assumption
    apply Set.diff_subset



/--
This rule can be used to transfer the set $`L` from $`L_W` to $`L_B`.
However, this requires that the postcondition $`Q` does not cause the PC
to point to a line from $`L`.
-/
theorem WL_TO_BL: ∀ (c : Code) (P Q : Assertion) (l : UInt64) (L_w L_b L : Set UInt64),
  L ⊂ L_w →
  (∀ (s:MState), Q s → s.pc ∉ L) →
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩⦃Q⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w \ L | L_b ∪ L⟩⦃Q⦄
  := by
  intros c P Q l L_w L_b L HLSubL_w HSPost TInter TEmpty
  unfold hoare_triple_up
  intros H _ _ s HCode  pre HPc
  specialize H TInter TEmpty s HCode  pre HPc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  unfold weak at H1
  specialize H1 HCode
  rcases H1 with ⟨n', ⟨H1', H2', H3', H4'⟩⟩
  unfold weak
  exists s'
  constructor
  . intros _
    exists n'
    try repeat (constructor <;> try assumption)
    apply HSPost
    exact H2
    intros n'' Hn''
    specialize H4' n'' Hn''
    apply MState.runNSteps_diff <;> try assumption
    simp
    constructor
    . intros hx h
      apply Set.mem_union_left ; apply Set.mem_of_subset_of_mem <;> try assumption
      apply Set.diff_subset
    . intros hx h
      apply Set.mem_union_left
      apply HLSubL_w.left h
  . constructor
    exact H2
    simp
    constructor
    . exact H3
    . apply HSPost
      exact H2



/--
Enables the merge of two Hoare-triples into one, given that the postcondition
of the first triple is equal to the precondition of the second triple.
-/
theorem S_SEQ': ∀(P R Q : Assertion) (c : Code) (l : UInt64) (L_w L_b L_w' L_b' : Set UInt64),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃R⦄ →
  (∀ l', l' ∈ L_w →
  c
  ⦃R⦄ l' ↦ ⟨L_w' | L_b'⟩ ⦃Q⦄) →
  c
  ⦃P⦄ l ↦ ⟨L_w' | L_b ∩ L_b'⟩ ⦃Q⦄
  := by
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoare_triple_up
  intros HFirst HSecond _ h_empty' s HCode HPc pre
  specialize HFirst TInter TEmpty s HCode HPc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  specialize HFirstWeak HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    simp
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  specialize HSecondWeak HCode'
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  . unfold weak
    intros HCode
    exists (m + m')
    constructor <;> try assumption
    . exact Nat.add_gt_zero _ _ HFW1
    . constructor <;> try assumption
      . rw [<- HFW2] at HSW2
        simp at HSW2
        exact HSW2
      . constructor <;> try assumption
        . intros m'' Hm''
          apply MState.run_n_plus_m_intersect' <;> assumption
  . constructor <;> try assumption
    . simp
      intros _
      exact HSecondPc



/--
Equal to `S_SEQ'`, but was defined for simplicity reasons.
`S_SEQ'` requires $`L_{B''}` to be in the form of $`L_B ∩ L_{B'}`.
This rule lets you apply S_SEQ with any form of $`L_{B''}` but asks for
a proof of $`L_{B''} = L_B ∩ L_{B'}`
-/
theorem S_SEQ {L_b'': Set UInt64}: ∀(P R Q : Assertion) (c : Code) (l : UInt64) (L_w L_b L_w' L_b' : Set UInt64),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃R⦄ →
  (∀ l':UInt64, l' ∈ L_w →
  c
  ⦃R⦄ l' ↦ ⟨L_w' | L_b'⟩ ⦃Q⦄) →
  L_b'' = L_b ∩ L_b' →
  c
  ⦃P⦄ l ↦ ⟨L_w' | L_b''⟩ ⦃Q⦄
  := by
  /-
  already shown in S_SEQ'
  -/
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoare_triple_up
  intros HFirst HSecond def_L_b'' _ h_empty' s HCode HPc pre
  specialize HFirst TInter TEmpty s HCode HPc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  specialize HFirstWeak HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    simp
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  specialize HSecondWeak HCode'
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  . unfold weak
    intros HCode
    exists (m + m')
    constructor <;> try assumption
    . exact Nat.add_gt_zero _ _ HFW1
    . constructor <;> try assumption
      . rw [<- HFW2] at HSW2
        simp at HSW2
        exact HSW2
      . constructor <;> try assumption
        . intros m'' Hm''
          rw [def_L_b'']
          apply MState.run_n_plus_m_intersect' <;> assumption
  . constructor <;> try assumption
    .
      rw [def_L_b'']
      simp
      intros _
      exact HSecondPc


/--
Allows to strenghten the precondition of a given Hoare-triple
-/
theorem PRE_STR : ∀(c : Code) (P1 P2 Q : Assertion) (L_w L_b : Set UInt64) (l : UInt64),
  (∀ (s : MState),
  s.code = c →
  (s.pc = l ∧ P2 s) → P1 s) →
  c
  ⦃P1⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P2⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by
  intros c P1 P2 Q L_w L_b l HTaut
  unfold hoare_triple_up
  intros H HInter HEmpty s HCode HPc pre
  apply H HInter <;> try assumption
  specialize HTaut s HCode
  . apply HTaut
    . constructor <;> try assumption


/--
Allows to weaken the postcondition of a given Hoare-triple
-/
theorem POST_WEAK : ∀(c : Code) (P Q1 Q2 : Assertion) (L_w L_b : Set UInt64) (l : UInt64),
  (∀ (s : MState),
  s.code = c →
  (s.pc ∈ L_w ∧ Q1 s) → Q2 s) →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q1⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q2⦄
  := by
  intros c P Q1 Q2 L_w L_b l
  unfold hoare_triple_up
  intros HTaut H HInter HEmpty  s HCode pre HPc
  specialize H HInter HEmpty s HCode pre HPc
  rcases H with ⟨s', ⟨P1, P2, P3⟩⟩
  exists s'
  constructor ; try assumption
  · constructor <;> try assumption
    · apply HTaut
      · unfold weak at P1
        specialize P1 HCode
        rcases P1 with ⟨_, _, K, _⟩
        rw [← K]
        simp
        exact HCode
      · constructor <;> try assumption
        · unfold weak at P1
          specialize P1 HCode
          rcases P1 with ⟨_, _, _, K, _⟩
          exact K



-- some notations for conjunction and negation of Assertions
private def Assertion.And (P Q : Assertion) : Assertion := fun st => (P st) ∧ (Q st)
private def Assertion.Not (P : Assertion) : Assertion := fun st => ¬(P st)

macro  a₁:term " ∧∧ " a₂:term : term => do
  `(Assertion.And $a₁ $a₂)

macro "∼" a:ident : term =>
  `(Assertion.Not $a)


/--
In this rule, a condition $`B` is evaluated and, depending on whether it is fulfilled or not,
either the command chain $`S_1` or $`S_2`$ is executed.
-/
theorem S_COND: ∀ (c : Code) (P C Q : Assertion) (l : UInt64)
  (L_w L_b : Set UInt64),
  c
  ⦃P ∧∧ C⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P ∧∧ ∼C⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃P⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by
  intros c P C Q l L_w L_b
  unfold hoare_triple_up
  intros h_RunCondTrue h_RunCondFalse h_LwInterLb h_LwNotEmpty s h_code h_pc pre
  specialize h_RunCondTrue h_LwInterLb h_LwNotEmpty s h_code
  specialize h_RunCondFalse h_LwInterLb h_LwNotEmpty s h_code
  apply excluded_middle_implication (P s) (C s)
  constructor
  . intros H
    specialize h_RunCondTrue h_pc H
    exact h_RunCondTrue
  . intros H
    specialize h_RunCondFalse h_pc H
    exact h_RunCondFalse
  exact pre


-- No formal proof. For informal proof contact me
/--
A rule to verify the formal correctness of a loop.
Requires:

* A Condition $`C`
* An Invariant $`I`
* A Variant $`V`

For more information, see the (documentation)[TODO insert link]
-/
theorem S_LOOP {α : Type} [Preorder α] [LT α] [WellFoundedLT α] :
    ∀ (Q C I : Assertion) (c : Code) (l : UInt64)
    (L_w L_b : Set UInt64) (V :MState → α),
  l ∉ L_w →
  l ∉ L_b →
  (∀ (x:α),
  c
  -- TODO: Introduce a notation for this (?)
  ⦃fun st => C st ∧ I st ∧ V st = x⦄
  l ↦ ⟨{l} ∪ L_w | L_b⟩
  ⦃fun st => V st < x ∧ I st ∧ st.pc = l⦄)
  →
  c
  ⦃fun st => ¬C st ∧ I st⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄ →
  c
  ⦃I⦄ l ↦ ⟨L_w | L_b⟩ ⦃Q⦄
  := by

  intros Q C I c l L_w L_b x h_lNinLw h_lNinL_b h_RunCondTrue h_RunCondFalse
  unfold hoare_triple_up
  intros h_inter h_empty s h_code h_pc pre
  have h_luLwInterLbEmpty:  ({l} ∪ L_w) ∩ L_b = ∅ := by
    rw [Set.union_inter_distrib_right]
    simp
    constructor
    . exact h_lNinL_b
    . exact h_inter
  have h_luLwNeqEmpty: {l} ∪ L_w ≠ ∅  := by
    rw [<- Set.nonempty_iff_ne_empty, Set.union_nonempty]
    right
    rw [Set.nonempty_iff_ne_empty]
    exact h_empty
  specialize h_RunCondFalse h_inter h_empty s h_code h_pc
  specialize h_RunCondTrue

  apply excluded_middle_implication (I s) (C s)
  constructor
  . intros H
    have asdf (x_1: α) : x s = x_1  := by sorry
    /-
    we know:
    ∀ (x' : α)
    C s ∧ I s ∧ x s = x' ∧ s.pc = l
    (s.runNSteps n) = s'
    x' < x s'
    I s'
    s'.pc = l

    also :
    α is well ordered

    because of this fact, this triple cannot be true ∀ (x' : α)
    So an assumption must we false

    I s / I s' **must** be true at all times
    s = x' can always be assigned
    s.pc = l is also always assignable
    =>
    The assumption, C is always true is false
    -/
    sorry
  . rintro ⟨H_I, H_Not_C⟩
    have : (fun st ↦ (¬C st ∧ I st)) s := by
      simp
      exact ⟨H_Not_C, H_I⟩
    specialize h_RunCondFalse this
    apply h_RunCondFalse
  exact pre

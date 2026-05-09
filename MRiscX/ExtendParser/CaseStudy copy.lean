import MRiscX.ExtendParser.Specifications

#check Assertion

theorem S_SEQ {L_b'': Set ProgramCounter}: ∀(P R Q : Assertion (MState Instr)) (c : (Code Instr))
      (l : ProgramCounter) (L_w L_b L_w' L_b' : Set ProgramCounter),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
      P R l L_w L_b c →
  (∀ l':UInt64, l' ∈ L_w →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    R Q l' L_w' L_b' c) →
  L_b'' = L_b ∩ L_b' →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w' L_b'' c
  := by
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoare_triple_up
  intros HFirst HSecond def_L_b'' _ h_empty' s HCode H_pc pre
  specialize HFirst TInter TEmpty s HCode H_pc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  simp at HFirstWeak
  simp at HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    unfold MState.getCode
    simp
  simp at *
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  simp at HSecondWeak
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  . unfold weak
    -- intros HCode
    exists (m + m')
    constructor <;> try assumption
    . simp [HFW1]
    . constructor <;> try assumption
      . rw [<- HFW2] at HSW2
        simp at HSW2
        exact HSW2
      . constructor <;> try assumption
        . intros m'' Hm''
          rw [def_L_b'']
          rw [MachineStateI_getPc_eq_mstate_getPc, Runnable_runNStep_eq_mstate_runNStep]
          apply MState.run_n_plus_m_intersect <;> try assumption
          repeat (simp ; assumption)
  . constructor <;> try assumption
    .
      rw [def_L_b'']
      simp
      intros _
      exact HSecondPc

theorem S_LOOP {α : Type} [Preorder α] [LT α] [WellFoundedLT α] :
    ∀ (Q C I : Assertion (MState Instr)) (code : (Code Instr)) (l : ProgramCounter)
    (L_w L_b : Set ProgramCounter) (V : (MState Instr) → α),
  l ∉ L_w →
  l ∉ L_b →
  (∀ (x : α),
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun st => C st ∧ I st ∧ V st = x) (fun st => V st < x ∧ I st ∧ st.pc = l)
    l ({l} ∪ L_w) L_b code) →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun st => ¬C st ∧ I st) Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    I Q l L_w L_b code
  := by
  intros Q C I code l L_w L_b V h_l_not_mem_Lw h_l_not_mem_Lb h_true h_false
  unfold hoare_triple_up
  intros h_inter h_nonempty s h_code h_pc hI

  have h_inter' : ({l} ∪ L_w) ∩ L_b = ∅ := by
    rw [Set.union_inter_distrib_right]
    simp
    constructor
    · exact h_l_not_mem_Lb
    · exact h_inter

  have h_nonempty' : ({l} ∪ L_w) ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty, Set.union_nonempty]
    right
    rw [Set.nonempty_iff_ne_empty]
    exact h_nonempty
  sorry

theorem weak_with_less_BL_weakens : ∀ (s s' : MState Instr) (L_w L_b L : Set ProgramCounter) ,
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter s s' L_w L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' L_w (L_b \ L)
  := by
  intros s s' L_w L_b L
  unfold weak
  intros H
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.mem_union, = Set.mem_diff]

theorem BL_SUBSET: ∀ (code : Code Instr) (P Q : Assertion (MState Instr)) (l: ProgramCounter)
    (L_w L_b L : Set ProgramCounter),
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w (L_b \ L) code
:= by
  intros c P Q l L_w L_b L T
  unfold hoare_triple_up
  intros H _ h_LwEmpty s HCode pre H_pc
  have L_b_sub : L_b \ L ⊆ L_b := by
    apply Set.diff_subset
  specialize H T h_LwEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  constructor
  · apply weak_with_less_BL_weakens ; exact H1
  · constructor
    · exact H2
    · apply Set.notMem_subset
      · exact L_b_sub
      · exact H3


theorem weak_L_w_with_L_from_L_b : ∀ (s s' : MState Instr) (L_w L_b L : Set ProgramCounter),
  L ⊆ L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' L_w L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' (L_w ∪ L) (L_b \ L)
  := by
  intros s s' L_w L_b L T
  unfold weak
  intros H
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.subset_def, = Set.mem_union, = Set.mem_diff]

theorem BL_TO_WL: ∀ (code : Code Instr) (P Q : Assertion (MState Instr)) (l : ProgramCounter)
    (L_w L_b L : Set ProgramCounter),
  L ⊆ L_b →
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  L_w ≠ ∅ →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l (L_w ∪ L) (L_b \ L) code
  := by
  intros c P Q l L_w L_b L TSub TInter TEmpty
  unfold hoare_triple_up
  intros H _ _ s HCode pre H_pc
  specialize H  TInter TEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  unfold weak
  constructor
  · apply weak_L_w_with_L_from_L_b <;> try assumption
  . constructor <;> try assumption
    apply Set.notMem_subset (t := L_b) <;> try assumption
    apply Set.diff_subset



instance : Preorder UInt64 where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp
  le_trans := by apply UInt64.le_trans
  lt_iff_le_not_ge := by
    intros a b
    constructor
    . intros h
      simp
      constructor
      . apply UInt64.le_of_lt h
      . exact h
    . simp


instance : WellFoundedLT UInt64 where
  wf := by
    simpa using (measure (fun x : UInt64 => x.toNat)).wf

  -- let P : α → Prop :=
  --   fun v =>
  --     ∀ s : MState Instr,
  --       s.code = code →
  --       s.pc = l →
  --       I s →
  --       V s = v →
  --       ∃ s', weak s s' L_w L_b code ∧ Q s' ∧ s'.pc ∉ L_b

  -- have loop_correct_at : ∀ v, P v := by
  --   let wf := (inferInstance : WellFoundedLT α).wf
  --   intro v0
  --   apply wf.induction v0
  --   intro v ih s h_code h_pc hI hV

  --   by_cases hC : C s
  --   · -- Guard true: run one loop iteration, then recurse on the smaller variant.
  --     have hpre : C s ∧ I s ∧ V s = v := by
  --       exact ⟨hC, hI, hV⟩

  --     specialize h_true v h_inter' h_nonempty' s h_code h_pc hpre

  --     rcases h_true with ⟨s', hweak', ⟨hVlt, hI', hpc'⟩, hnotinLb'⟩

  --     have h_code' : s'.code = code := by
  --       specialize hweak' h_code
  --       rcases hweak' with ⟨m, hm_pos, hrun, -, -⟩
  --       exact MState.code_remains_same s s' code m h_code hrun

  --     specialize ih (V s') hVlt s' h_code' hpc' hI' rfl

  --     rcases ih with ⟨s'', hweak'', hQ'', hnotinLb''⟩

  --     have hweak : weak s s'' L_w L_b code := by
  --       unfold weak
  --       intro h_code0

  --       specialize hweak' h_code0
  --       rcases hweak' with ⟨m, hm_pos, hrun, -, hsafe⟩

  --       specialize hweak'' h_code'
  --       rcases hweak'' with ⟨m', hm'_pos, hrun', hpc_in, hsafe'⟩

  --       refine ⟨m + m', Nat.add_gt_zero _ _ hm_pos, ?_, hpc_in, ?_⟩
  --       ·
  --         apply MState.runNSteps_add <;> try assumption
  --       · intro n hn
  --         apply MState.run_n_plus_m_pc_not_in_set (set := (L_w ∪ L_b)) <;> try assumption
  --         intro n' hn'
  --         rcases hn' with ⟨hn'le, hn'le_m⟩
  --         rw [Nat.le_iff_lt_or_eq] at hn'le_m
  --         cases hn'le_m with
  --         | inl hlt =>
  --             specialize hsafe n' ⟨hn'le, hlt⟩
  --             simp at hsafe
  --             push_neg at hsafe
  --             rcases hsafe with ⟨⟨-, hnotLw⟩, hnotLb⟩
  --             simp
  --             exact ⟨hnotLw, hnotLb⟩
  --         | inr heq =>
  --             simp
  --             rw [heq, hrun, hpc']
  --             exact ⟨h_l_not_mem_Lw, h_l_not_mem_Lb⟩

  --     exact ⟨s'', hweak, hQ'', hnotinLb''⟩

  --   · -- Guard false: discharge with the exit rule.
  --     exact h_false h_inter h_nonempty s h_code h_pc ⟨hC, hI⟩

  -- exact loop_correct_at (V s) s h_code h_pc hI rfl


def c_hamming_weight :=
  mriscx
    init:
      beq a1, zero, L4
      mv a5, a0
      slli a1, a1, 32
      srli a1, a1, 32
      add a3, a0, a1
      li a0, 0

    L3:
      lbu a4, 0(a5)
      cpop t0, a4
      add a4, a4, t0
      addi a5, a5, 1
      bne a5, a3, L3
    L4:
  end

def ms := {code := c_hamming_weight, registers := EmptyRegisters, memory := EmptyMemory , pc := 0,
            terminated := false: MState Instr}
#eval (ms.runNSteps 200).terminated
#eval (ms.runNSteps 200).registers



#check (2#8).cpop



open Lean Elab Tactic in
elab "prepare_second" : tactic => do
  evalTactic (←`(tactic| intros $(mkIdent `l') $(mkIdent `h_l')))
  let id_hl' := mkIdent `h_l'
  let id_hpc := mkIdent `h_pc
  let id_code := mkIdent `h_code'
  evalTactic (← `(tactic| simp at $id_hl':ident))
  evalTactic (←`(tactic| intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `ms)
                          $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `pre)))
  evalTactic (←`(tactic| try simp at $id_hpc:ident))
  evalTactic (←`(tactic| try simp at $id_code:ident))


open Lean Elab Tactic in
elab "solve_curr" : tactic => do
  evalTactic (←`(tactic| simp))
  evalTactic (←`(tactic| try unfold MState.getCurrInstr))
  evalTactic (←`(tactic| try unfold MState.getCode at $(mkIdent `h_code'):ident))
  evalTactic (←`(tactic| rw [$(mkIdent `h_pc):ident]))
  evalTactic (←`(tactic| try rw [$(mkIdent `h_l'):ident]))
  evalTactic (←`(tactic| rw [$(mkIdent `h_code'):ident]))
  evalTactic (←`(tactic| try unfold RegisterName.ofAbi!_zero ))
  evalTactic (←`(tactic| try unfold RegisterName.ofAbi? ))
  evalTactic (←`(tactic| try unfold RegisterNr.ofAbi? ))
  evalTactic (←`(tactic| try unfold RegisterNr.isAbiName ))
  evalTactic (←`(tactic| try unfold RegisterNr.abiNames))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_ofAbi!" : tactic => do
  evalTactic (←`(tactic| unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_ofAbi!" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE at $i:ident))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_rn_ofUint" : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE))

open Lean Elab Tactic in
elab "unfold_rn_ofUint" &"at" i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE at $i:ident))

open Lean Elab Tactic in
elab "unfold_rn_ofnat" : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofNat MRISCX_REG_SIZE))


open Lean Elab Tactic in
elab "unfold_rn_ofnat" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofNat MRISCX_REG_SIZE at $i:ident ))

open Lean Elab Tactic in
elab "simp_getRegisterAt" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold MState.getRegisterAt at $i:ident ))
  evalTactic (←`(tactic| unfold_rn_ofUint at $i:ident ))
  evalTactic (←`(tactic| simp at $i:ident))


open Lean Elab Tactic in
elab "simp_getRegisterAt" : tactic => do
  evalTactic (←`(tactic| unfold MState.getRegisterAt))
  evalTactic (←`(tactic| unfold_rn_ofUint))
  evalTactic (←`(tactic| simp))

/-
    li a0, 0

I: ∀ i, i < x[a5] - a → (x[a0] = UInt64.ofNat (∑ j : Fin (i).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat)
    loop:
      lbu a4, 0(a5)
      cpop t0, a4
      add a0, a0, t0
      addi a5, a5, 1
      bne a5, a3, loop
-/

set_option diagnostics true
theorem hamming_weight_correct (a length : UInt64):
  mriscx
    init:
      mv a5, a0
      li a0, 0
      beqz a1, finish
      add a3, a5, a1

    loop:
      lbu a4, 0(a5)
      cpop t0, a4
      add a0, a0, t0
      addi a5, a5, 1
      bne a5, a3, loop

    finish:
  end
  ⦃a.toNat + length.toNat < UInt64.size ∧ length > 0 ∧ x[a0] = a ∧ x[a1] = length ∧ ¬⸨terminated⸩⦄
  0 ↦ ⟨{9} | {n : ProgramCounter | n > 9 ∨ n = 0}⟩
  ⦃∀ i: UInt64, 0 <= i ∧ i < length → x[a0] = UInt64.ofNat ((∑ i : Fin UInt64.size , (((mem[UInt64.ofFin i])).cpop).toNat))
      ∧ ¬⸨terminated⸩⦄
  := by
  intros h_inter h_empty ms getcode getPc
  rintro ⟨no_overflow, h_a0, h_a1, h_terminated⟩
  -- cut between init and loop
  apply S_SEQ (P := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length) ∧ ¬⸨terminated⸩⦄)
              (R := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = 0 ∧ x[a1] = length ∧
                      x[a5] = a ∧ x[a3] = x[a5] + x[a1]) ∧ ¬⸨terminated⸩⦄)
              (L_w := {4})
              (L_b := {n : ProgramCounter | n > 4 ∨ n = 0})
              (L_b' := {n | n ≠ 9} \ {n : ProgramCounter | n < 9 ∨ n ≥ 4})
              <;> try assumption
  . simp
  . simp
  . simp
  . simp
  .
    (apply S_SEQ (P := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length) ∧ ¬⸨terminated⸩⦄)
                (R := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = 0 ∧ x[a1] = length ∧
                      x[a5] = a) ∧ ¬⸨terminated⸩⦄)
              (L_w := {3})
              (L_b := {n : ProgramCounter | n > 3 ∨ n = 0})
              (L_b' := {n : ProgramCounter | n ≠ 4}) <;> try assumption) ; simp ; simp ; simp ; simp
    .
      apply S_SEQ (P := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length) ∧ ¬⸨terminated⸩⦄)
                (R := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = 0 ∧ x[a1] = length ∧
                      x[a5] = a) ∧ ¬⸨terminated⸩⦄)
              (L_w := {2})
              (L_w' := {3})
              (L_b := {n : ProgramCounter | n > 2 ∨ n = 0})
              (L_b' := {n : ProgramCounter | n ≠ 3}) <;> try assumption
      . simp
      . simp
      . simp
      . simp
      .
        apply S_SEQ (P := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length) ∧ ¬⸨terminated⸩⦄)
                (R := ⦃(a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length ∧
                      x[a5] = a) ∧ ¬⸨terminated⸩⦄)
              (L_w := {1})
              (L_w' := {2})
              (L_b := {n : ProgramCounter | n ≠ 1})
              (L_b' := {n : ProgramCounter | n ≠ 2}) <;> try assumption
        . simp
        . simp
        . simp
        . simp
        . intros h_inter h_empty ms getcode getPc
          rintro ⟨⟨no_overflow, h_a0, h_a1⟩, h_terminated⟩
          simp at getcode
          apply spec_copyRegister
            (P := (⦃a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length ∧
                      x[a5] = a⦄))
             0 (RegisterName.ofAbi!_zero "a5") (RegisterName.ofAbi!_zero "a0")
            h_inter h_empty ms
          . simp
            unfold MState.getCurrInstr
            simp at getPc
            unfold MState.getCode at getcode
            rw [getPc, getcode]
            unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames
            simp
          . simp [getPc]
          . repeat (constructor <;> try assumption)
            unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames
            unfold MState.getRegisterAt MState.addRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE
            simp
            unfold RegisterNr.ofNat MRISCX_REG_SIZE
            unfold MState.getRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE at h_a0
            simp at h_a0
            have hw : { nr := 10, name := toString 10 : RegisterName} = { nr := 10, name := "a0" } := by
              rw [RegisterName.register_eq_on_nr']

            have : (TMap.get ms.registers { nr := 10, name := "a0" } = a) := by
                    rw [←hw]
                    exact h_a0
            have hj : { nr := 15, name := "a5" : RegisterName} = { nr := 15, name := toString 15 } := by
                    rw [RegisterName.register_eq_on_nr']
            simp
            rw [hj]
            simp [this, h_a0]
            exact t_update_eq
              (k := { nr := 15, name := toString 15 : RegisterName})
              (v := a)
              (t := ms.registers)
        . prepare_second
          rcases pre with ⟨⟨p1, p2, p3⟩, h_terminated⟩
          apply spec_li _ 1 (RegisterName.ofAbi!_zero "a0") 0 h_inter h_empty ms
          . solve_curr
          . simp [h_pc, h_l']
          . repeat (constructor <;> try assumption)

        . ext a
          simp
          grind
      . prepare_second
        rcases pre with ⟨⟨p1, p2, p3, p4⟩, h_terminated⟩
        apply spec_beqz_false _ 2 (RegisterName.ofAbi!_zero "a1") "finish" h_inter h_empty ms
        . solve_curr
        . simp [h_pc, h_l']
        . repeat (constructor <;> try assumption)
          unfold MState.getRegisterAt
          unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE
          simp
          have : { nr := 11, name := toString 11 : RegisterName} = { nr := 11, name := "a1" }
              := by
              rw [RegisterName.register_eq_on_nr']
          rw [←this]
          unfold MState.getRegisterAt at p3
          simp at p3
          unfold  RegisterNr.ofUInt64 MRISCX_REG_SIZE  at p3
          simp at *
          intros neq
          have hlen : length = 0 := by
            rw [←p3]
            exact neq
          contradiction
      . ext a ; simp ; grind
    . prepare_second
      rcases pre with ⟨⟨p1, p2, p3, p4⟩, h_terminated⟩
      apply spec_add _ 3  (RegisterName.ofAbi!_zero "a3")
                          (RegisterName.ofAbi!_zero "a5")
                          (RegisterName.ofAbi!_zero "a1")
                          h_inter h_empty
      . solve_curr
      . simp [h_pc, h_l']
      . repeat (constructor <;> try assumption)
        unfold_ofAbi!
        unfold MState.getRegisterAt MState.addRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE
        simp
        have h1 : { nr := 11, name := "a1" : RegisterName} = { nr := 11, name := toString (11:UInt64)} := by
          rw [RegisterName.register_eq_on_nr']
        have h2 : { nr := 13, name := "a3" : RegisterName} = { nr := 13, name := toString (13:UInt64)} := by
          rw [RegisterName.register_eq_on_nr']
        have h3 : { nr := 15, name := "a5" : RegisterName} = { nr := 15, name := toString (15:UInt64)} := by
          rw [RegisterName.register_eq_on_nr']
        rw [h1, h2, h3, t_update_eq]
    . ext a ; simp ; grind
  .
    intros l' hl'
    rw [hl']
    intros h_inter h_empty ms h_code' h_pc pre
    apply S_LOOP
      (C := ⦃x[a5] ≠ x[a3]⦄)
      (I := ⦃(x[a0] = UInt64.ofNat (∑ j : Fin (x[a5] - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
              ∧ x[a3] = a + length
              ∧ x[a5] < a + length
              ∧ x[a5] ≥ a
              ∧ x[a1] = length)
              ∧ ¬⸨terminated⸩⦄)
      (V := ⦃a + length - x[a5]⦄)
      (l := 4)
      (L_w := {9})
      (L_b := {n | n ≠ 9} \ {n : ProgramCounter | n < 9 ∨ n ≥ 4})
      (code :=  mriscx
                  init:
                      mv a5, a0;
                      li a0, 0;
                      beqz a1, finish;
                      add a3, a5, a1;

                  loop:
                      lbu a4, 0(a5);
                      cpop t0, a4;
                      add a0, a0, t0;
                      addi a5, a5, 1;
                      bne a5, a3, loop;

                  finish: end)
    . simp
    . simp
    . intros x h_inter h_empty ms h_code' h_pc pre
      apply S_SEQ (P := ⦃(a.toNat + length.toNat < UInt64.size
                        ∧ x[a0] = UInt64.ofNat (∑ j : Fin ((x[a5] + 1) - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
                        ∧ x[a3] = a + length
                        ∧ x[a5] < a + length
                        ∧ x[a5] ≥ a
                        ∧ x[a1] = length) ∧ ¬⸨terminated⸩⦄ )
                (R := ⦃(a.toNat + length.toNat < UInt64.size
                        ∧ x[a0] = UInt64.ofNat (∑ j : Fin (x[a5] - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
                        ∧ x[a3] = a + length
                        ∧ x[a5] < a + length
                        ∧ x[a5] ≥ a
                        ∧ x[a1] = length
                        ∧ x[a4] = mem_ub[x[a5]]
                        ∧ x[t0] = UInt64.ofBitVec ((mem_ub[x[a5]].toBitVec).cpop.zeroExtend 64))
                        ∧ ¬⸨terminated⸩⦄)
              (L_w := {8})
              (L_b := {n : ProgramCounter | n > 8 ∨ n ≤ 4})
              (L_b' := {n : ProgramCounter | n ≠ 4} \ {9}) <;> try assumption
      . simp
      . simp
      . ext a ; simp ; grind
      .
        rw [Set.subset_def]
        simp
      . apply S_SEQ (P := _ )
                (R := ⦃(a.toNat +length.toNat < UInt64.size
                        ∧ x[a0] = UInt64.ofNat (∑ j : Fin ((x[a5]) - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
                        ∧ x[a3] = a + length
                        ∧ x[a5] < a + length
                        ∧ x[a5] ≥ a
                        ∧ x[a1] = length
                        ∧ x[a4] = mem_ub[x[a5]]
                        ∧ x[t0] = UInt64.ofBitVec ((mem_ub[x[a5]].toBitVec).cpop.zeroExtend 64))
                        ∧ ¬⸨terminated⸩⦄)
              (L_w := {7})
              (L_w' := {8})
              (L_b := {n : ProgramCounter | n > 7 ∨ n ≤ 4})
              (L_b' := {n : ProgramCounter | n ≠ 8}) <;> try assumption
        . simp
        . simp
        . simp
        . simp
        . apply S_SEQ (P := _ )
                (R := ⦃(a.toNat + length.toNat < UInt64.size
                        ∧ x[a0] = UInt64.ofNat (∑ j : Fin (x[a5] - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
                        ∧ x[a3] = a + length
                        ∧ x[a5] < a + length
                        ∧ x[a5] ≥ a
                        ∧ x[a1] = length
                        ∧ x[a4] = mem_ub[x[a5]]
                        ∧ x[t0] = UInt64.ofBitVec ((mem_ub[x[a5]].toBitVec).cpop.zeroExtend 64))
                        ∧ ¬⸨terminated⸩⦄)
              (L_w := {6})
              (L_w' := {7})
              (L_b := {n : ProgramCounter | n > 6 ∨ n ≤ 4})
              (L_b' := {n : ProgramCounter | n ≠ 7}) <;> try assumption
          . simp
          . simp
          . simp
          . simp
          . apply S_SEQ (P := _ )
                (R := ⦃(a.toNat +length.toNat < UInt64.size
                        ∧ x[a0] = UInt64.ofNat (∑ j : Fin (x[a5] - a).toNat,
                                            ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))
                        ∧ x[a3] = a + length
                        ∧ x[a5] < a + length
                        ∧ x[a5] ≥ a
                        ∧ x[a1] = length
                        ∧ x[a4] = mem_ub[x[a5]])
                        ∧ ¬⸨terminated⸩⦄)
              (L_w := {5})
              (L_w' := {6})
              (L_b := {n : ProgramCounter | n > 5 ∨ n ≤ 4})
              (L_b' := {n : ProgramCounter | n ≠ 6}) <;> try assumption
            . simp
            . simp
            . simp
            . simp
            . sorry
            .
              -- CPOP
              prepare_second
              -- rcases pre with ⟨⟨p1, ⟨p2, p3⟩⟩, h_terminated⟩
              apply spec_cpop _ 5 (RegisterName.ofAbi!_zero "t0") (RegisterName.ofAbi!_zero "a4")
                h_inter h_empty ms
              . solve_curr
              . simp [h_l', h_pc]
              .
                repeat (constructor <;> try assumption)
                rcases pre with ⟨⟨p2, p3, p4, p5, p6, p7, p8⟩, h_terminated⟩
                unfold_ofAbi!
                unfold MState.getRegisterAt MState.addRegisterAt
                simp only [Bool.false_eq_true, ↓reduceIte]
                have h10 : (RegisterNr.ofUInt64 10 == 0) = false := by
                    decide
                -- rw [←h10]
                unfold_rn_ofUint

                simp
                intros neq
                unfold MState.getRegisterAt at p4
                unfold_rn_ofUint at p4
                simp at p4

                rw [p4] at neq
                simp_getRegisterAt at p5
                rw [neq] at p5
                apply UInt64.lt_irrefl
                exact p5
                rcases pre with ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8⟩, h_terminated⟩

                constructor
                exact p2
                constructor
                exact p3
                constructor
                assumption
                constructor
                assumption
                constructor
                assumption
                constructor
                assumption
                constructor
                assumption
                unfold MState.getRegisterAt MState.addRegisterAt
                unfold_rn_ofUint
                unfold_ofAbi!
                have h1 : { nr := 5, name := "t0" : RegisterName}
                              = { nr := 5, name := toString (5:UInt64)}
                        := by
                        rw [RegisterName.register_eq_on_nr']
                rw [←h1, t_update_eq]

                unfold MState.loadByte_unsigned MState.loadByte_raw
                simp
                .
                  apply asdf
                  unfold MState.getRegisterAt at p8
                  unfold_rn_ofUint at p8
                  simp at *
                  have h1 : { nr := 14, name := "a4" : RegisterName} =
                             { nr := 14, name := toString (14:UInt64) } := by
                              rw [RegisterName.register_eq_on_nr']
                  rw [h1, p8]
                  rfl
                .
                  rcases pre with ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8⟩, h_terminated⟩
                  exact h_terminated
                  -- constructor
            . ext a ; simp ; grind
            --       .  assumption
            --       . constructor
            --         . assumption
            --         . constructor
            --           . assumption
            --           . constructor
            --             . rw [←h2, p6]
            --               unfold MState.loadByte_unsigned MState.loadByte_raw
            --               simp [p6]
            --             . apply asdf
            --               simp [p6]
            --               rfl
            --     have jh : { nr := 5, name := "t0" : RegisterName} =
            --                 { nr := 5, name := toString (5:UInt64)} := by
            --       rw [RegisterName.register_eq_on_nr']
            --     rw [jh]
            --     rw [t_update_eq]

            --     unfold MState.getRegisterAt at p1
            --     simp [h10] at p1
            --     exact p1
            --     . apply RegisterName.register_neq_on_nr
            --       decide
            --     . constructor
            --       .
            --         rcases pre with ⟨⟨p1, ⟨p2, p3, p4, p5, p6⟩⟩, h_terminated⟩
            --         unfold MState.addRegisterAt MState.getRegisterAt
            --         unfold_ofAbi!
            --         unfold_rn_ofUint
            --         simp
            --         unfold MState.getRegisterAt at p2
            --         unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE at p2
            --         simp at p2
            --         rw [p2]
            --       .
            --         rcases pre with ⟨⟨p1, ⟨p2, p3, p4, p5, p6⟩⟩, h_terminated⟩
            --         have h2: { nr := 14, name := "a4" : RegisterName}
            --                   = { nr := 14, name := toString (14:UInt64)} := by
            --                   rw [RegisterName.register_eq_on_nr']


            --         unfold MState.getRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE at p6
            --         simp at p6
            --         rw [←h2] at p6
            --         unfold_ofAbi!
            --         unfold_rn_ofUint
            --         unfold MState.addRegisterAt MState.getRegisterAt
            --         simp
            --         have h1 : { nr := 5, name := "t0" : RegisterName}
            --                   = { nr := 5, name := toString (5:UInt64)}
            --                 := by
            --                 rw [RegisterName.register_eq_on_nr']
            --         rw [←h1, t_update_eq]

            --         unfold MState.loadByte_unsigned MState.loadByte_raw
            --         simp
            --         .
            --           constructor
            --           .  assumption
            --           . constructor
            --             . assumption
            --             . constructor
            --               . assumption
            --               . constructor
            --                 . rw [←h2, p6]
            --                   unfold MState.loadByte_unsigned MState.loadByte_raw
            --                   simp [p6]
            --                 . apply asdf
            --                   simp [p6]
            --                   rfl
            --     . rcases pre with ⟨_, h_terminated⟩
            --       exact h_terminated
            -- . ext a ; simp ; grind
          . prepare_second
            apply spec_add _ 6 (RegisterName.ofAbi!_zero "a0")
                (RegisterName.ofAbi!_zero "a0") (RegisterName.ofAbi!_zero "t0")
                h_inter h_empty ms
            . solve_curr
            . simp [h_l', h_pc]
            .
              rcases pre with ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩, h_terminated⟩
              repeat (constructor <;> try assumption)
              unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi?
                RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE
              unfold MState.getRegisterAt MState.addRegisterAt
              unfold MState.getRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE at p9
              simp at p9


              unfold_rn_ofUint
              -- unfold_ofAbi!
              have h1 : { nr := 10, name := "a0" : RegisterName }
                          = { nr := 10, name := toString (10:UInt64)} := by
                          rw [RegisterName.register_eq_on_nr']
              have h2 : { nr := 5, name := "t0" : RegisterName }
                          = { nr := 5, name := toString (5:UInt64)} := by
                          rw [RegisterName.register_eq_on_nr']
              simp [h1, t_update_eq]
              unfold MState.getRegisterAt MState.getMemoryAt RegisterNr.ofUInt64 MRISCX_REG_SIZE at p3
              simp at p3
              rw [p3]
              unfold MState.getMemoryAt
              simp
              rw [h2, p9]
              unfold MState.loadByte_unsigned MState.loadByte_raw
              simp
              unfold Finset.sum Fin.val
              simp
              sorry
              . repeat (constructor ; assumption)
                unfold MState.getRegisterAt MState.addRegisterAt MState.loadByte_unsigned MState.loadByte_raw
                unfold_rn_ofUint
                unfold_ofAbi!
                unfold MState.getRegisterAt RegisterNr.ofUInt64 MRISCX_REG_SIZE at p9
                simp at p9
                rw [p9]
                unfold MState.loadByte_unsigned MState.loadByte_raw
                simp
          . ext a ; simp ; grind
        .
          prepare_second
          apply spec_addi _ 7 (RegisterName.ofAbi!_zero "a5") (RegisterName.ofAbi!_zero "a5") 1
                h_inter h_empty ms
          . solve_curr
          . simp [h_l', h_pc]
          . sorry
        . ext a ; simp ; grind
      . prepare_second
        -- apply BL_SUBSET
        apply BL_TO_WL
          (P := ⦃
                (a.toNat + length.toNat < UInt64.size
                ∧( ∀ i, i < x[a5] - a → (x[a0] = UInt64.ofNat (∑ j : Fin (i).toNat,
                  ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))))

                ∧ x[a3] = a + length
                ∧ x[a5] < a + length
                ∧ x[a5] ≥ a
                ∧ x[a1] = length) ∧ ¬⸨terminated⸩
                ⦄)
          <;> try assumption
        . simp
        . simp
        . simp
        . intros h_inter h_empty ms h_code' h_pc pre

          apply spec_bne_true
                (⦃
                (a.toNat + length.toNat < UInt64.size
                ∧( ∀ i, i < x[a5] - a → (x[a0] = UInt64.ofNat (∑ j : Fin (i).toNat,
                  ((mem[a + (UInt64.ofNat j.toNat)]).cpop.toNat))))

                ∧ x[a3] = a + length
                ∧ x[a5] < a + length
                ∧ x[a5] ≥ a
                ∧ x[a1] = length) ∧ ¬⸨terminated⸩
                ⦄)
             8 (RegisterName.ofAbi!_zero "a5") (RegisterName.ofAbi!_zero "a3") "loop" 4
            h_inter h_empty ms


/-
∃ s',
    weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter ms s' {4} {n | n ≠ 4} ∧
      (fun st =>
            ((a.toNat + length.toNat < UInt64.size ∧
                  (∀ i < st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } - a,
                      st.getRegisterAt { nr := RegisterNr.ofUInt64 10, name := toString 10 } =
                        UInt64.ofNat (∑ j, (BitVec.cpop (st.getMemoryAt (a + UInt64.ofNat j.toNat))).toNat)) ∧
                    st.getRegisterAt { nr := RegisterNr.ofUInt64 13, name := toString 13 } = a + length ∧
                      st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } < a + length ∧
                        st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } ≥ a ∧
                          st.getRegisterAt { nr := RegisterNr.ofUInt64 11, name := toString 11 } = length) ∧
                ¬st.terminated = true) ∧
              ¬st.terminated = true)
          s' ∧
        MachineStateI.getPc Instr (Code Instr) RegisterName UInt64 s' ∉ {n | n ≠ 4}
with the goal
  ∃ s',
    weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter ms s' {4} {n | n ≠ 4} ∧
      (fun st =>
            a + length - st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } < x ∧
              ((st.getRegisterAt { nr := RegisterNr.ofUInt64 10, name := toString 10 } =
                      UInt64.ofNat (∑ j, (BitVec.cpop (st.getMemoryAt (a + UInt64.ofNat j.toNat))).toNat) ∧
                    st.getRegisterAt { nr := RegisterNr.ofUInt64 13, name := toString 13 } = a + length ∧
                      st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } < a + length ∧
                        st.getRegisterAt { nr := RegisterNr.ofUInt64 15, name := toString 15 } ≥ a ∧
                          st.getRegisterAt { nr := RegisterNr.ofUInt64 11, name := toString 11 } = length) ∧
                  ¬st.terminated = true) ∧
                st.pc = 4)
          s' ∧
        MachineStateI.getPc Instr (Code Instr) RegisterName UInt64 s' ∉ {n | n ≠ 4}
-/

              -- rw [←BitVec.cpop_eq_sum]
              -- cases UInt64.lt_or_eq_of_le ih with
              -- | inl v =>
              --   specialize p3 i v
              --   rw [p3, p9]






              -- unfold_rn_ofUint
              -- unfold MState.getMemoryAt --MState.loadByte_unsigned MState.loadByte_raw
              -- simp
              -- have h1 : {nr := 10, name := "a0" : RegisterName} =
              --   {nr := 10, name := toString (10:UInt64)} := by
              --   rw [RegisterName.register_eq_on_nr']
              -- have h2 : {nr := 5, name := "t0" : RegisterName} =
              --   {nr := 5, name := toString (5:UInt64)} := by
              --   rw [RegisterName.register_eq_on_nr']
              -- rw [h1, h2]
              -- simp only [t_update_eq]


              -- unfold MState.getRegisterAt at p7
              -- unfold MState.getRegisterAt at p1
              -- unfold_rn_ofUint at p7
              -- unfold_rn_ofUint at p1
              -- simp at p7
              -- simp at p1
              -- rw [p7, p1]


              -- rw [t_update_neq]



    sorry






          /-


  ∃ s',
    weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter ?s s' {9} {n | n > 9 ∨ n ≤ 4} ∧
      ?Q s' ∧ MachineStateI.getPc Instr (Code Instr) RegisterName UInt64 s' ∉ {n | n > 9 ∨ n ≤ 4}
with the goal
  ∃ s',
    weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter ms s' {9} {n | n > 9 ∨ n = 0} ∧
      (fun st =>
            ∀ (i : UInt64),
              0 ≤ i ∧ i < length →
                st.getRegisterAt { nr := RegisterNr.ofUInt64 10, name := toString 10 } =
                    { toBitVec := BitVec.zeroExtend 64 (BitVec.cpop (st.getMemoryAt (a + i))) } ∧
                  ¬st.terminated = true)
          s' ∧
        MachineStateI.getPc Instr (Code Instr) RegisterName UInt64 s' ∉ {n | n > 9 ∨ n = 0}


     -/

      .
      .
  . sorry
  . simp
    intros pc w
    grind
  . repeat (constructor <;> try assumption)

  -- sorry

theorem hamming_weight_correct': hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
          (fun ms => ms.terminated = false) (fun ms => ms.terminated = false)
          0 ({11}) ({n:ProgramCounter | n > 11 ∨ n = 0})
          (mriscx
            init:
              beq a1, zero, L4
              mv a5, a0
              slli a1, a1, 32
              srli a1, a1, 32
              add a3, a0, a1
              li a0, 0

            L3:
              lbu a4, 0(a5)
              cpop t0, a4
              add a4, a4, t0
              addi a5, a5, 1
              bne a5, a3, L3
            L4:
          end) := by
      intros h_inter h_empty ms getcode
      sorry

#check hoare_triple_up Instr (Code Instr) RegisterName

-- section GenericHoareNotationExample

-- variable (α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType : Type)
-- variable [Runnable α]
-- variable [MachineStateI α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType]

-- theorem generic_hoare_notation_works :
--     ∀ (code : CodeType) (P Q : Assertion α)
--       (l : ProgramCounterType) (L_w L_b L : Set ProgramCounterType),
--       code
--       ⦃P⦄ l ↦ ⟨L_w | L_b \ L⟩⦃Q⦄ →
--       code
--       ⦃P⦄ l ↦ ⟨L_w | L_b \ L⟩⦃Q⦄ := by
--   intro code P Q l L_w L_b L h
--   exact h

-- end GenericHoareNotationExample

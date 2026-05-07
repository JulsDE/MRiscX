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


theorem asdf :
  mriscx
    init:
      li x2, 1
      li x3, 2
  end
  ⦃¬⸨terminated⸩⦄
  0 ↦ ⟨{1} | {n : ProgramCounter | n  ≠ 1}⟩
  ⦃x[x2] = 1 ∧ ¬⸨terminated⸩⦄
  := by
  intros h_inter h_empty ms h_code h_pc t_terminated

  sorry

def ad : Byte := 12
#check ⦃⸨pc⸩ = 2⦄
#check fun (st:MState Instr) => st.pc = 2

#eval ad.cpop.zeroExtend 64
#check UInt64.ofBitVec

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
  ⦃∀ i: UInt64, 0 <= i ∧ i < length → x[a3] = (UInt64.ofBitVec (mem[a + i].cpop.zeroExtend 64))
      ∧ ¬⸨terminated⸩⦄
  := by
  intros h_inter h_empty ms getcode getPc
  rintro ⟨no_overflow, h_a0, h_a1, h_terminated⟩
  apply S_SEQ (P := ⦃a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length ∧ ¬⸨terminated⸩⦄)
              (R := ⦃a.toNat + length.toNat < UInt64.size ∧ x[a0] = a ∧ x[a1] = length ∧
                      x[a5] = length ∧ x[a3] = x[a5] + x[a1] ∧ ¬⸨terminated⸩⦄)
              (L_w := {4})
              (L_b := {n : ProgramCounter | n > 4 ∨ n = 0}) <;> try assumption
  . simp
  . simp
  . simp
  .
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

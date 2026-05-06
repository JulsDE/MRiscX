import MRiscX.ExtendParser.Specifications

#check Assertion

theorem S_SEQ {L_b'': Set ProgramCounter}: ∀(P R Q : Assertion (MState Instr)) (c : (Code Instr))
      (l : ProgramCounter) (L_w L_b L_w' L_b' : Set ProgramCounter),
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
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoare_triple_up
  intros HFirst HSecond def_L_b'' _ h_empty' s HCode H_pc pre
  specialize HFirst TInter TEmpty s HCode H_pc pre
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
          apply MState.run_n_plus_m_intersect <;> assumption
  . constructor <;> try assumption
    .
      rw [def_L_b'']
      simp
      intros _
      exact HSecondPc


#check mriscx
        first:
      end

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


theorem hamming_weight_correct :
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
  ⦃¬⸨terminated⸩⦄
  0 ↦ ⟨{11} | {n : ProgramCounter | n > 11 ∨ n = 0}⟩
  ⦃¬⸨terminated⸩⦄
  := by
  intros h_inter h_empty ms getcode getPc h_terminated

  sorry

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

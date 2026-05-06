import MRiscX.ExtendParser.Specifications

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

import MRiscX.ExtendParser.MStateTheory

theorem spec_li :
  specification_LoadImmediate := by
  sorry

theorem spec_lbu :
  specification_LoadByteUnsigned := by
  unfold specification_LoadByteUnsigned
  intros P pc rd off rs h_inter h_neq ms curr getPc
  rintro ⟨P_true, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    simp
    constructor
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc
    . intros n' h
      aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        simp [h_terminated, curr]
        unfold MState.addRegisterAt MState.getMemAddrFromReg
        unfold MState.addRegisterAt MState.getMemAddrFromReg at P_true
        simp at *
        by_cases h : rd.nr = 0
        . simp [h] at P_true
          simp [h]
          rw [←h_terminated]
          exact P_true
        .
          simp [h] at P_true
          simp [h]
          rw [←h_terminated]
          unfold MState.loadByte_unsigned MState.loadByte_raw
          unfold MState.loadByte_unsigned MState.loadByte_raw at P_true
          simp at *
          exact P_true
      . unfold MState.runOneStep execute
        simp [h_terminated, curr]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc


theorem spec_beq_true:
  specification_JumpEq_true := by
  unfold specification_JumpEq_true
  intros P pc r1 r2 label newPc h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_label, h_eq, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  unfold MState.getLabelAt MState.getCode at h_label
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_eq]
          unfold MState.jump
          simp [h_label]
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_eq]
        simp [h_label]
        exact P_true
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_eq]
        unfold MState.jump
        simp [h_label]
        exact h_terminated
    . unfold MState.runOneStep execute
      simp [h_terminated, curr, h_eq]
      simp [h_label]
      unfold MState.setPc
      simp


theorem spec_beq_false:
  specification_JumpEq_false := by
  unfold specification_JumpEq_false
  intros P pc r1 r2 label h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_neq, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_neq]
          exact h_getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        exact P_true
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        exact h_terminated
    . unfold MState.runOneStep execute
      simp [h_terminated, curr, h_neq]
      exact h_getPc


theorem spec_copyRegister:
  specification_CopyRegister := by
  unfold specification_CopyRegister
  intros P pc rd rs h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_getPc]
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        unfold MState.addRegisterAt MState.getRegisterAt
        unfold MState.addRegisterAt MState.getRegisterAt at P_true
        simp at *
        by_cases h : rd.nr = 0
        . simp [h] at *
          exact P_true
        . simp [h] at *
          exact P_true
      . unfold MState.runOneStep execute
        simp [h_terminated, curr]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact h_getPc

theorem spec_cpop :
  specification_CountSetBits := by
  unfold specification_CountSetBits
  intros P pc rd rs h_inter h_neq s curr getPc
  rintro ⟨pre, h_terminated⟩
  exists s.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp
          exact getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp
        unfold MState.getRegisterAt at pre
        unfold MState.addRegisterAt at pre
        unfold MState.addRegisterAt
        simp at pre
        by_cases h: rd.nr = 0
        . rw [h] at pre
          simp at pre
          simp [h]
          exact pre
        . simp [h] at pre
          simp [h]
          rw [←sum_eq_cpop']
          unfold MState.getRegisterAt
          simp
          exact pre
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_terminated]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc

theorem spec_slli :
  specification_ShiftLeftImmediate := by
  unfold specification_ShiftLeftImmediate
  intros P pc rd rs i h_inter h_neq s curr getPc
  rintro ⟨pre, h_terminated⟩
  exists s.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp
          exact getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp
        unfold MState.getRegisterAt at pre
        unfold MState.addRegisterAt at pre
        unfold MState.addRegisterAt
        simp at pre
        by_cases h : rd.nr = 0
        . rw [h] at pre
          simp at pre
          simp [h]
          exact pre
        . simp [h] at pre
          simp [h]
          unfold MState.getRegisterAt
          simp
          exact pre
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_terminated]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc

theorem spec_srli :
  specification_ShiftRightImmediate := by
  unfold specification_ShiftRightImmediate
  intros P pc rd rs i h_inter h_neq s curr getPc
  rintro ⟨pre, h_terminated⟩
  exists s.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp
          exact getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp
        unfold MState.getRegisterAt at pre
        unfold MState.addRegisterAt at pre
        unfold MState.addRegisterAt
        simp at pre
        by_cases h : rd.nr = 0
        . rw [h] at pre
          simp at pre
          simp [h]
          exact pre
        . simp [h] at pre
          simp [h]
          unfold MState.getRegisterAt
          simp
          exact pre
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_terminated]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc

theorem spec_add :
  specification_Add := by
  unfold specification_Add
  intros P pc rd rs1 rs2 h_inter h_neq s curr getPc
  rintro ⟨pre, h_terminated⟩
  exists s.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp
          exact getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp
        unfold MState.getRegisterAt at pre
        unfold MState.addRegisterAt at pre
        unfold MState.addRegisterAt
        simp at pre
        by_cases h : rd.nr = 0
        . rw [h] at pre
          simp at pre
          simp [h]
          exact pre
        . simp [h] at pre
          simp [h]
          unfold MState.getRegisterAt
          simp
          exact pre
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_terminated]
    . unfold MState.runOneStep execute
      simp [h_terminated, curr]
      exact getPc

theorem spec_bne_true:
  specification_JumpNeq_true := by
  unfold specification_JumpNeq_true
  intros P pc r1 r2 label newPc h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_label, h_neq, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  unfold MState.getLabelAt MState.getCode at h_label
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_neq]
          unfold MState.jump
          simp [h_label]
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        simp [h_label]
        exact P_true
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        unfold MState.jump
        simp [h_label]
        exact h_terminated
    . unfold MState.runOneStep execute
      simp [h_terminated, curr, h_neq]
      simp [h_label]
      unfold MState.setPc
      simp

theorem spec_bne_false:
  specification_JumpNeq_false := by
  unfold specification_JumpNeq_false
  intros P pc r1 r2 label h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_eq, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_eq]
          exact h_getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_eq]
        exact P_true
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_eq]
        exact h_terminated
    . unfold MState.runOneStep execute
      simp [h_terminated, curr, h_eq]
      exact h_getPc



theorem spec_beqz_true :
  specification_JumpEqZero_true := by
  unfold specification_JumpEqZero_true hoare_triple_up_1
  intros P pc r lbl newPc hinter hneq s curr getPc
  rintro ⟨P_true, hlbl, hreg, h_terminated⟩
  simp at curr
  simp at getPc
  simp at h_terminated
  unfold MState.getLabelAt MState.getCode at hlbl
  exists s.runOneStep
  simp
  constructor
  unfold weak
  exists 1
  simp
  constructor
  . unfold MState.runOneStep execute
    rw [h_terminated, curr]
    simp
    unfold MState.jump
    rw [hlbl, hreg]
    simp
  . intros n' hn'
    intros hneq
    rw [hneq] at hn'
    contradiction
  . constructor
    . unfold MState.runOneStep execute
      rw [h_terminated, curr]
      simp
      unfold MState.jump
      rw [hlbl]
      simp
      unfold MState.setPc at P_true
      rw [hreg]
      simp
      exact ⟨P_true, h_terminated⟩
    . unfold MState.runOneStep execute
      rw [h_terminated, curr]
      simp [hreg]
      apply runOneStep_jump_succ' <;> assumption

theorem spec_beqz_false :
  specification_JumpEqZero_false := by
  unfold specification_JumpEqZero_false
  intros P pc r label h_inter h_notEmpty ms curr h_getPc
  rintro ⟨P_true, h_neq, h_terminated⟩
  exists ms.runOneStep
  unfold weak
  simp at *
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      . simp
      . constructor
        . unfold MState.runOneStep execute
          rw [h_terminated, curr]
          simp [h_neq]
          exact h_getPc
        . intros n' hn'
          aesop
  . constructor
    . constructor
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        exact P_true
      . unfold MState.runOneStep execute
        rw [h_terminated, curr]
        simp [h_neq]
        exact h_terminated
    . unfold MState.runOneStep execute
      simp [h_terminated, curr, h_neq]
      exact h_getPc

import MRiscX.Semantics.Theory
import MRiscX.Tactics.ProofAutomationTactics
import MRiscX.Elab.HoareElaborator
import MRiscX.Elab.CodeElaborator
import MRiscX.Delab.DelabHoare
open Lean Elab Tactic

/-
Specifications
-/
/-
This file holds the specifications of each instruction introduced
in Instr.lean (excluding the panic instruction).
Additionally, its using the syntax defined in Syntax.lean.
Moreover, the Notation for the Hoare logic from the
file HoareElaborator.lean is used.

With the knowledge of this file it is clear, that the intereprete function
runOneStep works as intended. Because of this, this assembly language can be
used to write algorithms and prove their correctness.

For certifying the instruction, the rule of assignment (P ⟦x[r] ← v; pc++⟧) is used.
The hoare triples state that if you start in a state where the precondition P holds,
and you execute the instruction, the precondition P will still
hold after the execution. The precondition is applied after simulating the
effects of the instruction.
-/
theorem specification_LoadAddress (P: Assertion) (l r v : UInt64):
  hoare
    ⟪la x r, v;⟫
    ⦃P ⟦x[r] ← v; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩
  -- rw [pre2] at pre1
  simp at h_terminated
  unfold MState.addRegister at pre
  unfold weak
  exists s.runOneStep
  apply And.intro
  case left =>
      intros _
      exists 1
      apply And.intro
      simp
      case right =>
        simp [<- MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep
        rw [h_terminated, ←h_pc, HCurr]
        simp
        zero_lt_ne_zero
  case right =>
      simp [- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep MState.getRegisterAt
      rw [HCurr]
      simp
      simp [h_terminated, ←h_pc]
      simp at pre
      rw [h_terminated] at pre
      rw [h_pc]
      rw [h_pc] at pre
      exact pre

theorem specification_LoadImmediate (P: Assertion) (l r v : UInt64):
  hoare
    ⟪li x r, v;⟫
    ⦃P ⟦x[r] ← v; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
    unfold hoare_triple_up_1
    rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩
    simp at h_terminated
    unfold weak
    exists s.runOneStep
    apply And.intro
    case left =>
      intros _
      exists 1
      apply And.intro
      simp
      case right =>
        simp [<- MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep
        rw [h_terminated, ←h_pc, HCurr]
        simp
        zero_lt_ne_zero
    case right =>
      -- try rw [xor_iff_notation] at pre
      simp [- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep
      rw [HCurr]
      simp
      simp [h_terminated, ←h_pc]
      simp at pre
      rw [h_terminated] at pre
      rw [h_pc]
      rw [h_pc] at pre
      exact pre



theorem specification_CopyRegister (P: Assertion) (l r v : UInt64):
  hoare
    ⟪mv x r, x v;⟫
    ⦃P ⟦x[r] ← x[v]; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_AddImmediate (P: Assertion) (l d r v : UInt64):
  hoare
    ⟪addi x d, x r, v;⟫
    ⦃P ⟦x[d] ← (x[r] + v) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_Increment (P: Assertion) (l d : UInt64):
  hoare
    ⟪inc x d;⟫
    ⦃P ⟦x[d] ← (x[d] + 1) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_AddRegister (P: Assertion) (l d r1 r2 : UInt64):
  hoare
    ⟪add x d, x r1, x r2;⟫
    ⦃P ⟦x[d] ← (x[r1] + x[r2]) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_SubImmediate (P: Assertion) (l d r : UInt64):
  hoare
    ⟪subi x d, x r, l;⟫
    ⦃P ⟦x[d] ← (x[r] - l) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_Decrement (P: Assertion) (l d : UInt64):
  hoare
    ⟪dec x d;⟫
    ⦃P ⟦x[d] ← (x[d] - 1) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_SubRegister (P: Assertion) (l d r1 r2 : UInt64):
  hoare
    ⟪sub x d, x r1, x r2;⟫
    ⦃P ⟦x[d] ← (x[r1] - x[r2]) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification


theorem specification_XorImmediate (P: Assertion) (l d r : UInt64):
  hoare
    ⟪xori x d, x r, l;⟫
    ⦃P ⟦x[d] ← (x[r] ^^^ l) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩
  simp at h_terminated
  unfold weak
  exists s.runOneStep
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    case right =>
      simp [<- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep
      rw [h_terminated, <-h_pc, HCurr]
      simp
      zero_lt_ne_zero
  case right =>
    simp at pre
    simp [-MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.getRegisterAt
    rw [h_terminated, HCurr]
    simp
    simp [h_pc]
    rw [h_pc] at pre
    exact ⟨pre, h_terminated⟩

theorem specification_XOR (P: Assertion) (l d r1 r2 : UInt64):
  hoare
    ⟪xor x d, x r1, x r2;⟫
    ⦃P ⟦x[d] ← (x[r1] ^^^ x[r2]) ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ s HCurr h_pc ⟨pre, h_terminated⟩
  simp at h_terminated
  unfold weak
  exists s.runOneStep
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    case right =>
      simp [<- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep
      rw [h_terminated, <-h_pc, HCurr]
      simp
      zero_lt_ne_zero
  case right =>
    simp at pre
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.getRegisterAt
    rw [h_terminated, HCurr]
    simp
    simp [h_pc]
    rw [h_pc] at pre
    exact ⟨pre, h_terminated⟩

theorem specification_LoadWordImmediate (P: Assertion) (l d m : UInt64):
  hoare
    ⟪lw x d, m;⟫
    ⦃P ⟦x[d] ← mem[m] ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification


theorem specification_LoadWordReg (P: Assertion) (l d m : UInt64):
  hoare
    ⟪lw x d, x m;⟫
    ⦃P ⟦x[d] ← mem[x[m]] ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification


theorem specification_StoreWordImmediate (P: Assertion) (l d r : UInt64):
  hoare
    ⟪sw x r, x d;⟫
    ⦃P ⟦mem[x[d]] ← x[r] ; pc++⟧ ∧ ¬⸨terminated⸩⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l+1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoare_simp_specification

theorem specification_Jump (P : Assertion) (l newPc : UInt64) (label : String):
  hoare
    ⟪j label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_label, h_terminated⟩
  simp at h_terminated
  simp at h_label
  unfold MState.currInstruction at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . constructor ; simp
      simp
      simp [<- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep MState.jump
      rw [h_terminated]
      simp [h_curr, h_label]

      zero_lt_ne_zero
  case right =>
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jump
    unfold MState.setPc at pre
    rw [h_terminated]
    rw [h_terminated] at pre
    simp [h_curr, h_label, pre]


theorem specification_Jump' (P : Assertion) (l newPc : UInt64) (label : String):
  hoare
    ⟪j label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩ ∧ ⸨pc⸩ = newPc⦄
  end := by
  unfold hoare_triple_up_1
  rintro h_inter h_empty state h_curr h_pc ⟨pre, h_label, h_terminated⟩
  simp at h_terminated
  simp at h_label
  simp at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . constructor ; simp
      simp
      simp [<- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep MState.jump
      rw [h_terminated]
      simp [h_curr, h_label]

      zero_lt_ne_zero
  case right =>
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jump
    unfold MState.setPc at pre
    rw [h_terminated]
    rw [h_terminated] at pre
    simp [h_curr, h_label, pre]


theorem specification_JumpEq_true (P : Assertion) (l newPc r1 r2: UInt64) (s : String):
  hoare
    ⟪beq x r1, x r2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[r1] = x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_label, h_cond, h_terminated⟩
  simp at h_terminated
  simp at h_label
  simp at h_cond
  unfold MState.currInstruction at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . constructor ; simp
      simp
      simp [<- MState.run_one_step_eq_run_n_1]
      unfold MState.runOneStep MState.jump MState.jif' MState.jump
      rw [h_terminated]
      simp [h_curr, h_label, h_cond]

      zero_lt_ne_zero
  case right =>
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jump MState.jif' MState.jump
    unfold MState.setPc at pre
    rw [h_terminated]
    rw [h_terminated] at pre
    simp [h_curr, h_label, h_cond, pre]


theorem specification_JumpEq_false (P : Assertion) (l r1 r2: UInt64) (s : String):
  hoare
    ⟪beq x r1, x r2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[r1] ≠ x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩
  simp at h_terminated
  simp at h_cond
  simp at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . repeat (constructor <;> try simp)
    -- . constructor ; simp
      . simp [<- MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep  MState.jif' MState.jump
        rw [h_terminated, ← h_pc]
        simp [h_curr, h_cond]
      . zero_lt_ne_zero
  case right =>
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jif' MState.jump
    rw [h_terminated]
    -- rw [h_terminated] at pre
    simp [h_curr, h_cond]
    rw [← h_pc, h_terminated]
    simp
    simp [ h_terminated] at pre
    exact pre


theorem specification_JumpNeq_true (P : Assertion) (l newPc r1 r2: UInt64) (s : String):
  hoare
    ⟪bne x r1, x r2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[r1] ≠ x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec

theorem specification_JumpNeq_false (P : Assertion) (l r1 r2: UInt64) (s : String):
  hoare
    ⟪bne x r1, x r2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[r1] = x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec



theorem specification_JumpGt_true (P : Assertion) (l newPc r1 r2: UInt64) (s : String):
  hoare
    ⟪bgt x r1, x r2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[r1] > x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec



theorem specification_JumpGt_false (P : Assertion) (l r1 r2: UInt64) (s : String):
  hoare
    ⟪bgt x r1, x r2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[r1] ≤ x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩
  simp at h_terminated
  simp at h_cond
  simp at h_curr
  have h_cond_false: (TMap.get state.registers r2 < TMap.get state.registers r1) ↔ false := by
    simp
    exact h_cond
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . repeat (constructor <;> try simp)
    -- . constructor ; simp
      . simp [<- MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep  MState.jif' MState.jump
        rw [h_terminated, ← h_pc]
        simp [h_curr]
        simp only [h_cond_false]
        simp
      . zero_lt_ne_zero
  case right =>
    simp [-MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jif' MState.jump
    rw [h_terminated]
    simp [h_curr]
    rw [← h_pc, h_terminated]
    simp only [h_cond_false]
    simp
    simp [h_terminated] at pre
    exact pre


theorem specification_JumpLe_true (P : Assertion) (l newPc r1 r2: UInt64) (s : String):
  hoare
    ⟪ble x r1, x r2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[r1] ≤ x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec


theorem specification_JumpLe_false (P : Assertion) (l r1 r2: UInt64) (s : String):
  hoare
    ⟪ble x r1, x r2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[r1] > x[r2] ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩
  simp at h_terminated
  simp at h_cond
  simp at h_curr
  simp at pre
  rw [← UInt64.not_le] at h_cond
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro; simp
    . repeat (constructor <;> try simp)
      . simp [<- MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep MState.jif' MState.jump
        rw [h_terminated, ←h_pc]
        simp [h_curr, h_cond]
      . zero_lt_ne_zero
  case right =>
    simp [- MState.run_one_step_eq_run_n_1]
    unfold MState.runOneStep MState.jif' MState.jump
    rw [h_terminated, ← h_pc]
    simp [h_curr, h_cond, pre]
    exact h_terminated


theorem specification_JumpEqZero_true (P : Assertion) (l newPc r: UInt64) (label : String):
  hoare
    ⟪beqz x r, label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ x[r] = 0 ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec




theorem specification_JumpEqZero_false (P : Assertion) (l r: UInt64) (label : String):
  hoare
    ⟪beqz x r, label;⟫
    ⦃P ⟦pc++⟧ ∧ x[r] ≠ 0 ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec




theorem specification_JumpNeqZero_true (P : Assertion) (l newPc r: UInt64) (s : String):
  hoare
    ⟪bnez x r, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = some newPc ∧ x[r] ≠ 0 ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{newPc} | {n:UInt64 | n ≠ newPc}⟩
    ⦃P ⟦⟧⦄
  end
  := by
  simp_jump_spec



theorem specification_JumpNeqZero_false (P : Assertion) (l r: UInt64) (s : String):
  hoare
    ⟪bnez x r, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[r] = 0 ∧ ¬⸨terminated⸩⦄
    l ↦ ⟨{l + 1} | {n:UInt64 | n ≠ l+1}⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simp_jump_spec

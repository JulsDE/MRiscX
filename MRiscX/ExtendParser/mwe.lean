import MRiscX.ExtendParser.GenerateAll
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
-- import MRiscX.ExtendParser.GenerateInstrSpecification
import MRiscX.Hoare.HoareCore

#check ({1}:Set Nat)


mkAll RV64 Instr execute
  PANIC:
    {
      syntax : PANIC,
      semantics: fun ms => (MState.setTerminated ms true),
      specification: True
    }
  LoadAddress:
    {
      syntax : la (a:register), (m:immediate),
      semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
      specification:  ⦃P ⟦x[a] <- m; pc++⟧ ∧ ¬⸨terminated⸩⦄
                      pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄}
  LoadImmediate:
    {
      syntax : li (a:register), (m:immediate),
      semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
      specification:  ⦃P ⟦x[a] <- m; pc++⟧ ∧ ¬⸨terminated⸩⦄
                      pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
    }
  Jump:
    {
      syntax : j (lbl:label),
      semantics: fun ms => (MState.jump ms lbl),
      specification:  ⦃P ⟦pc ← newPc⟧ ∧ labels[lbl] = some newPc ∧ ¬⸨terminated⸩⦄
                      pc ↦ ⟨{newPc} | {n : ProgramCounter | n ≠ newPc}⟩
                      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
    }
  JumpEqZero:
    {
      syntax : beqz (r:register) (lbl:label),
      semantics: fun ms =>  if (MState.getRegisterAt ms r == 0) then
                              MState.jump ms lbl
                            else
                              MState.incPc ms
                            ,
      specification:  ⦃P ⟦pc ← newPc⟧ ∧ labels[lbl] = some  newPc ∧ x[r] = 0 ∧ ¬⸨terminated⸩⦄
                      pc ↦ ⟨{newPc} | {n : ProgramCounter | n ≠ newPc}⟩
                      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄

    }


def MState.runOneStep (ms : MState Instr) :=
  execute ms (ms.getCurrInstr)

def MState.runNSteps (ms : MState Instr) (n : Nat) :=
  match n with
  | 0 => ms
  | n' + 1 => MState.runNSteps (ms.runOneStep) n'

instance instRunable : runable (MState Instr) where
  runOneStep := MState.runOneStep
  runNSteps := MState.runNSteps
#check mriscx
        first :
                li x3, 1
                li x 33, 1
                li t0, 1
        end
def c := mriscx
        f: li x1, 1
        end

@[simp]
theorem MachineStateI_getPc_eq_mstate_getPc (ms : MState Instr) :
  MachineStateI.getPc Instr (Code Instr) RegisterName UInt64 ms = ms.pc := by
    unfold MachineStateI.getPc instMState
    simp

@[simp]
theorem MachineStateI_getCode_eq_mstate_Code (ms : MState Instr) :
  MachineStateI.getCode Instr RegisterName UInt64 ProgramCounter ms = ms.getCode := by
    unfold MachineStateI.getCode instMState
    simp

@[simp]
theorem MachineStateI_currInstr_eq_mstate_currInstr (ms : MState Instr) :
  MachineStateI.currInstruction (Code Instr) RegisterName UInt64 ProgramCounter ms =
    ms.getCurrInstr := by
    unfold MachineStateI.currInstruction instMState
    simp

@[simp]
theorem runable_runOneStep_eq_mstate_runOneStep (ms : MState Instr) :
  runable.runOneStep ms = ms.runOneStep := by
  unfold runable.runOneStep instRunable
  simp

@[simp]
theorem runable_runNStep_eq_mstate_runNStep (ms : MState Instr) :
  runable.runNSteps ms = ms.runNSteps := by
  unfold runable.runNSteps instRunable
  simp

@[simp]
theorem runNSteps_1_eq_runOneStep (ms : MState Instr) :
  ms.runNSteps 1 = ms.runOneStep := by
  unfold MState.runNSteps MState.runNSteps
  simp

@[simp]
theorem runOneStep_jump_succ' : ∀ (s : MState Instr) (label : String) (newPc : ProgramCounter),
  s.getLabelAt label = some newPc →
  s.terminated = false →
  (s.jump label).pc = newPc := by
  intros s label newPc hlabel h_terminated
  unfold MState.getLabelAt at hlabel
  unfold MState.getCode at hlabel
  unfold MState.jump
  rw [h_terminated, hlabel]


@[simp]
theorem runOneStep_jump_succ : ∀ (s : MState Instr) (label : String) (newPc : ProgramCounter),
  s.getCurrInstr = Instr.Jump label →
  s.getLabelAt label = some newPc →
  s.terminated = false →
  s.runOneStep.pc = newPc := by
  intros s label newPc curr hlabel h_terminated
  unfold MState.runOneStep execute
  unfold MState.getLabelAt at hlabel
  unfold MState.getCode at hlabel
  simp at *
  rw [h_terminated, curr]
  simp
  unfold MState.jump
  rw [hlabel]


theorem ms_addRegiseter_pc_eq_pc : ∀ (ms : MState Instr) (r : RegisterName) (v : UInt64),
    (MState.addRegisterAt ms r v).pc = ms.pc := by
  unfold MState.addRegisterAt
  intros ms r v
  by_cases d: r.nr = 0 <;> simp [d]


def triple :=
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun ms => MState.terminated ms = false)
    (fun ms => ms.getRegisterAt (RegisterName.mk (RegisterNr.ofNat 1) "x1") = 1 ∧ ms.terminated = false)
    0
    {1}
    {n : UInt64 | n ≠ 1}
    c
/-
P : Assertion
pc dst addr : UInt64
L : Set UInt64
⊢ L = {n | n ≠ pc + 1} →
  hoare_triple_up_1 (fun st => P (st.incPc.addRegister dst addr) ∧ ¬st.terminated = true)
    (fun st => P st ∧ ¬st.terminated = true) pc {pc + 1} L (Instr.LoadAddress dst addr)

-/
#print specification_LoadImmediate
#print specification_Jump
#print specification_JumpEqZero

theorem spec_beqz :
  specification_JumpEqZero := by
  unfold specification_JumpEqZero hoare_triple_up_1
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


theorem spec_j :
  specification_Jump := by
  unfold specification_Jump hoare_triple_up_1
  intros P pc lbl newPc h_inter h_L_w s curr get_pc pre
  sorry

theorem spec_la  :
    specification_LoadAddress := by
  unfold specification_LoadAddress hoare_triple_up_1
  intros P pc dst val h j ms l n
  rintro ⟨i, o⟩
  simp at o
  rw [MachineStateI_currInstr_eq_mstate_currInstr] at l
  rw [MachineStateI_getPc_eq_mstate_getPc] at n
  exists ms.runOneStep
  unfold weak
  constructor
  . exists 1
    constructor
    . simp
    . constructor
      .
        rw [runable_runNStep_eq_mstate_runNStep, runNSteps_1_eq_runOneStep]
      . constructor
        . rw [MachineStateI_getPc_eq_mstate_getPc]
          unfold MState.runOneStep execute
          simp
          rw [o, l]
          simp
          unfold MState.incPc
          simp
          rw [ms_addRegiseter_pc_eq_pc]
          exact n
        . rintro n' ⟨left, right⟩
          simp at right
          rw [right] at left
          contradiction
  . constructor
    . simp
      constructor
      . unfold MState.runOneStep execute
        rw [l]
        simp
        have : (ms.addRegisterAt dst val).incPc = ms.incPc.addRegisterAt dst val := by
          unfold MState.addRegisterAt MState.incPc
          rw [o]
          by_cases d: dst.nr = 0 <;> simp [d]
          exact o
        rw [this]
        rw [o]
        simp at *
        exact i
      . unfold MState.runOneStep execute
        rw [l]
        simp
        unfold MState.addRegisterAt
        by_cases d: dst.nr = 0 <;> (simp [d] ; unfold MState.incPc ; rw [o] ; simp)
    . rw [MachineStateI_getPc_eq_mstate_getPc]
      unfold MState.runOneStep execute
      rw [l]
      simp
      unfold MState.incPc
      simp [ms_addRegiseter_pc_eq_pc]
      rw [o]
      simp
      exact n

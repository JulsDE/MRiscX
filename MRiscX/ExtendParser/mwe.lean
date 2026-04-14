import MRiscX.ExtendParser.GenerateInstrAndSyntax
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
-- import MRiscX.ExtendParser.GenerateInstrSpecification
import MRiscX.Hoare.HoareCore



mkAll RV64 Instr execute
  PANIC:
    { syntax : PANIC,
      semantics: fun ms => (MState.setTerminated ms true),
      specification: True }
  LoadAddress:
    { syntax : la (a:register), (m:immediate),
      semantics: fun (ms) => (MState.addRegisterAt ms a m).incPc,
      specification: ⦃P ⟦x[a] <- m; pc++⟧⦄ pc ↦ ⟨{pc + 1} | {n : UInt64 | n ≠ pc + 1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄}
  LoadImmediate:
    { syntax : li (a:register), (m:immediate),
      semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
      specification: true }
  Jump:
    { syntax : j (lbl:label),
      semantics: fun ms => (MState.jump ms lbl),
      specification: True }

def MState.runOneStep (ms : MState Instr) :=
  execute ms (ms.getCurrInstr)

def MState.runNSteps (ms : MState Instr) (n : Nat) :=
  match n with
  | 0 => ms
  | n' + 1 => MState.runNSteps (ms.runOneStep) n'

instance instRunable : runable (MState Instr) where
  runOneStep := MState.runOneStep
  runNSteps := MState.runNSteps

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

theorem spec_la (P : Assertion (MState Instr)) (pc : ProgramCounter) (dst val : UInt64) :
    specification_LoadAddress P pc dst val:= by
  unfold specification_LoadAddress hoare_triple_up_1
  intros h j ms l n p
  -- rintro ⟨i, o⟩
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
          rw [l]
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
        exact i
      . unfold MState.runOneStep execute
        rw [l]
        simp
        unfold MState.addRegisterAt
        by_cases d: dst.nr = 0 <;> (simp [d] ; unfold MState.incPc ; simp ; exact o)
    . rw [MachineStateI_getPc_eq_mstate_getPc]
      unfold MState.runOneStep execute
      rw [l]
      simp
      unfold MState.incPc
      simp [ms_addRegiseter_pc_eq_pc]
      exact n
  sorry

theorem spec_li (dst : RegisterName) (val : UInt64) (P : Assertion (MState Instr))
          (pc : ProgramCounter) :
  hoare_triple_up_1 (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun ms => P (ms.incPc.addRegisterAt dst val) ∧  ms.terminated = false)
    (fun ms => P ms ∧  ms.terminated = false)
    pc
    {pc + 1}
    {n : ProgramCounter | n ≠ pc + 1}
    (Instr.LoadImmediate dst val)
  := by
  unfold hoare_triple_up_1
  intros h j ms l n
  rintro ⟨i, o⟩
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
          rw [l]
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
        exact i
      . unfold MState.runOneStep execute
        rw [l]
        simp
        unfold MState.addRegisterAt
        by_cases d: dst.nr = 0 <;> (simp [d] ; unfold MState.incPc ; simp ; exact o)
    . rw [MachineStateI_getPc_eq_mstate_getPc]
      unfold MState.runOneStep execute
      rw [l]
      simp
      unfold MState.incPc
      simp [ms_addRegiseter_pc_eq_pc]
      exact n







theorem test : triple := by
  unfold triple hoare_triple_up c
  intros h j ms l n m
  rw [MachineStateI_getPc_eq_mstate_getPc] at n
  exists ms.runOneStep
  unfold weak
  rw [MachineStateI_getCode_eq_mstate_Code] at l
  unfold MState.getCode at l
  simp
  constructor
  exists 1
  constructor
  simp
  constructor
  simp
  constructor
  unfold MState.runOneStep execute MState.getCurrInstr
  rw [l, n]
  simp
  unfold MState.addRegisterAt MState.incPc RegisterNr.ofNat MRISCX_REG_SIZE
  simp
  rw [m]
  simp
  exact n
  intros n' hn'
  grind
  constructor
  unfold MState.runOneStep execute MState.getCurrInstr MState.addRegisterAt MState.getRegisterAt
  rw [m, l, n]
  simp
  unfold RegisterNr.ofNat MRISCX_REG_SIZE MState.incPc
  simp
  exact m
  unfold MState.runOneStep execute MState.getCurrInstr
  rw [m, l, n]
  simp
  unfold MState.addRegisterAt MState.incPc RegisterNr.ofNat MRISCX_REG_SIZE
  simp
  exact n



-- mkSpecs abd

import MRiscX.ExtendParser.ISADef


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
theorem Runnable_runOneStep_eq_mstate_runOneStep (ms : MState Instr) :
  Runnable.runOneStep ms = ms.runOneStep := by
  unfold Runnable.runOneStep instRunnable
  simp

@[simp]
theorem Runnable_runNStep_eq_mstate_runNStep (ms : MState Instr) :
  Runnable.runNSteps ms = ms.runNSteps := by
  unfold Runnable.runNSteps instRunnable
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

@[simp]
theorem MState.incPc_eq_pc_plus_one (ms : MState Instr) :
  ms.incPc = {ms with pc := ms.pc + 1} := by
  unfold MState.incPc
  simp

open Lean Elab Tactic in
elab "simp_addRegisterAt" : tactic => do
  evalTactic (←`(tactic| unfold $(mkIdent `MState.addRegisterAt)))
  evalTactic (←`(tactic| by_cases h: $(mkIdent `rd.nr) == 0 <;> simp [h]))

@[simp]
theorem MState.addRegisterAt_no_change_at_mem (ms : MState Instr) (rd : RegisterName) (v : UInt64) :
  (ms.addRegisterAt rd v).memory = ms.memory := by
  simp_addRegisterAt

@[simp]
theorem MState.addRegisterAt_no_change_at_code (ms : MState Instr) (rd : RegisterName) (v : UInt64) :
  (ms.addRegisterAt rd v).code = ms.code := by
  simp_addRegisterAt

@[simp]
theorem MState.addRegisterAt_no_change_at_pc (ms : MState Instr) (rd : RegisterName) (v : UInt64) :
  (ms.addRegisterAt rd v).pc = ms.pc := by
  simp_addRegisterAt

@[simp]
theorem MState.addRegisterAt_no_change_at_terminated (ms : MState Instr) (rd : RegisterName) (v : UInt64) :
  (ms.addRegisterAt rd v).terminated = ms.terminated := by
  simp_addRegisterAt

@[simp]
theorem MState.jump_eq_setPc (ms : MState Instr) (lbl : String) (newPc : ProgramCounter) :
    ms.getLabelAt lbl = some newPc →
    ms.jump lbl = ms.setPc newPc := by
  intros h
  unfold MState.jump MState.setPc
  unfold MState.getLabelAt MState.getCode at h
  simp [h]

@[simp]
theorem MState.getLabel_unpack (ms : MState Instr) (label : String) :
  ms.getLabelAt label = PMap.get ms.code.labelMap label := by
  unfold MState.getLabelAt
  rfl

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
theorem MState.unfold_getRegisterAt : ∀ (ms : MState Instr) (r : RegisterName),
  r.nr ≠ 0 →
  ms.getRegisterAt r = TMap.get ms.registers r := by
  intros ms r h
  unfold MState.getRegisterAt
  simp [h]

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

@[simp]
theorem MState.runNSteps_zero (ms : MState Instr) :
  ms.runNSteps 0 = ms := by
  unfold MState.runNSteps
  rfl


@[simp]
theorem MState.runNSteps_plus_one (n : Nat) : ∀ (ms : MState Instr),
  ms.runNSteps (n + 1) = (ms.runOneStep).runNSteps n := by
  induction n with
  | zero =>
    unfold MState.runNSteps
    simp
  | succ n' IHn' =>
    intros ms
    unfold MState.runNSteps
    rw [IHn']

@[simp]
theorem MState.runNSteps_runOneStep_comm : ∀ (ms : MState Instr) (n : Nat),
  (ms.runNSteps n).runOneStep = (ms.runOneStep).runNSteps n := by
  intros ms n
  revert ms
  induction n with
  | zero => simp
  | succ n' IHn' =>
    intros ms
    nth_rw 1 [runNSteps_plus_one]
    rw [IHn']
    rw [runNSteps_plus_one]

@[simp]
theorem MState.runNSteps_plus_one' (n : Nat) : ∀ (ms : MState Instr),
  ms.runNSteps (n + 1) = (ms.runNSteps n).runOneStep := by
  induction n with
  | zero =>
    unfold MState.runNSteps
    simp
  | succ n' IHn' =>
    intros ms
    unfold MState.runNSteps
    conv =>
      lhs
      unfold MState.runNSteps


    sorry


@[simp]
theorem MState.runNSteps_comm (ms : MState Instr)  : ∀ (n m : Nat),
  (ms.runNSteps n).runNSteps m = (ms.runNSteps m).runNSteps n := by
  intros n
  induction n with
  | zero => simp
  | succ n' IHn' =>
    intros m
    sorry

@[simp]
theorem MState.runNSteps_assoc (ms : MState Instr) (m n : Nat) :
  (ms.runNSteps n).runNSteps m = (ms.runNSteps (n + m)) := by
  induction n with
  | zero =>
    simp
  | succ n' IHn' =>sorry

@[simp]
theorem MState.runOneStep_code_stays (ms : MState Instr) :
  ms.runOneStep.code = ms.code := by
  unfold MState.runOneStep execute
  by_cases terminated : ms.terminated = true
  . simp [terminated]
  . simp
    -- cases ms.getCurrInstr  <;> simp [terminated]

    cases h : ms.getCurrInstr with
    | PANIC =>
      unfold MState.setTerminated
      simp [terminated]
    | Jump a =>
      unfold MState.jump
      simp [terminated]
      cases PMap.get ms.code.labelMap a with
      | some l =>
        simp
      | none =>
        simp
    | JumpEqZero r lbl =>
      unfold MState.setTerminated MState.jump
      simp [terminated]
      by_cases j: ms.getRegisterAt r = 0 <;> simp [j]
      cases PMap.get ms.code.labelMap lbl <;> simp

    | JumpEq r1 r2 lbl =>
      simp [terminated]
      unfold MState.jump
      by_cases j: ms.getRegisterAt r1 = ms.getRegisterAt r2 <;> simp [j]
      cases j: PMap.get ms.code.labelMap lbl <;> simp
    | JumpNeq r1 r2 lbl =>
      simp [terminated]
      unfold MState.jump
      by_cases j: ms.getRegisterAt r1 = ms.getRegisterAt r2 <;> simp [j]
      cases j: PMap.get ms.code.labelMap lbl <;> simp

    | _ => simp [terminated]

@[simp]
theorem MState.runNSteps_code_stays  (n : Nat) : ∀ (ms : MState Instr),
  (ms.runNSteps n).code = ms.code := by
  induction n with
  | zero =>  simp
  | succ n' IHn' =>
    intros ms
    simp
    rw [IHn']
    simp

--------------------- Hoare theory


theorem MState.run_n_plus_m_intersect : ∀ (s s' : MState Instr) (m m' : Nat) (L_w L_b L_w' L_b' : Set ProgramCounter),
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  s.runNSteps m = s' →
  s'.pc ∈ L_w →
  s'.pc ∉ L_b →
  (∀ (n : ℕ), 0 < n ∧ n < m → (s.runNSteps n).pc ∉ L_w ∪ L_b) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ L_w' ∪ L_b') →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ L_w' ∪ L_b ∩ L_b'
:= by
  intros s s' m m' L_w L_b L_w' L_b' h_sets h_run1 h_pc_w h_pc_not_b h_safe1 h_safe2 n'' HN''
  rcases HN'' with ⟨h_pos, h_lt⟩
  rcases h_sets with ⟨h_Lw'SubL_b, h_LwInterLw'⟩
  -- n'' ≤ m → s.runNSteps n'' ∉ L_b ∧ s.runNSteps n'' ∈ L_w → s.runNSteps n'' ∉ (L_w' ∪ L_b), da L_w ∩ L_w' = ∅
  -- n'' > m → s.runNSteps n'' ∉ L_w' ∪ L_b'
  rw [Set.union_inter_distrib_left]
  by_cases h: n'' ≤ m
  . cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have h_n'': 0 < n'' ∧ n'' < m := And.intro h_pos hlt
      specialize h_safe1 n'' h_n''
      have h_safe1_NinLw': (s.runNSteps n'').pc ∉ L_w' ∪ L_b:= by
        rw [Set.mem_union]
        simp
        rw [Set.mem_union] at h_safe1
        simp at h_safe1
        rcases h_safe1 with ⟨_, h_safe1_r⟩
        constructor
        . apply Set.notMem_subset (a:= (s.runNSteps n'').pc) (s := L_w') (t := L_b) ; repeat assumption
        . exact h_safe1_r
      intros h_in
      exact h_safe1_NinLw' (Set.mem_of_mem_inter_left h_in)
    | inr heq =>
      have h_safe1_m: (s.runNSteps n'').pc ∉ L_w' ∪ L_b := by
        rw [heq]
        rw [Set.mem_union]
        simp
        constructor
        . apply Set.notMem_subset (a:= (s.runNSteps m).pc) (s := L_w') (t := L_b)
          exact h_Lw'SubL_b
          rw [h_run1]
          exact h_pc_not_b
        . rw [h_run1]
          exact h_pc_not_b
      intros h_in
      exact h_safe1_m (Set.mem_of_mem_inter_left h_in)
  . push_neg at h
    -- n'' > m ⇒ ∃ n' such that n'' = m + n'
    let n' := n'' - m
    have h_pos : 0 < n' := by
      apply Nat.sub_pos_of_lt h
    have hn'_lt : n' < m' := by
      -- n'' < m + m' ⇒ n' = n'' - m < m'
      dsimp only [n']
      grind
    have h_run_eq : s.runNSteps n'' = s'.runNSteps n' := by
      dsimp only [n']
      rw [← h_run1]
      simp
      rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      apply Nat.le_of_lt h
    rw [h_run_eq]
    have hn'_pre : 0 < n' ∧ n' < m' := by
      constructor <;> try assumption
    specialize h_safe2 n' hn'_pre
    intro h_in
    exact h_safe2 (Set.mem_of_mem_inter_right h_in)

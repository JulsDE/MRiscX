import MRiscX.ExtendParser.GenerateAll
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
-- import MRiscX.ExtendParser.GenerateInstrSpecification
import MRiscX.Hoare.HoareCore
import Mathlib.Algebra.Polynomial.BigOperators


-- Reference specification of the SHA-256 σ₀ function, defined once.
def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))


def σ₀ (x : UInt32) : UInt32 :=
  (rotr32 x 7) ^^^ (rotr32 x 18) ^^^ (x >>> 3)

-- Machine-state helpers: extract the low 32 bits of a register and
-- sign-extend a 32-bit result back into a 64-bit register (RV64 Zknh64).
def lo32  (w : UInt64) : UInt32 := w.toUInt32
def sext32 (x : UInt32) : UInt64 := UInt64.ofBitVec (x.toBitVec.signExtend 64)

def MState.applySig0 {InstrType} (ms : MState InstrType) (dst src : RegisterName)
    : (MState InstrType) :=
  ms.addRegisterAt dst (sext32 (σ₀ (lo32 (ms.getRegisterAt src))))

-- theorem asdf: ∀ (w : Nat) (v : BitVec (w + 1)),
--   BitVec.cpopNatRec v (w + 1) 0 = v.cpopNatRec (w) 0 + (v.getLsbD (w + 1)).toNat := by
--   simp

theorem sum_getLsbD_eq_cpopNatRec : ∀ (w : Nat) (v : BitVec w),
    (∑ i : Fin w, (v.getLsbD i).toNat) = v.cpopNatRec w 0 := by
  intros w
  induction w with
  | zero =>
    simp
  | succ n' IHn' =>
    intro v
    rw [BitVec.cpopNatRec_succ]

    -- split the Fin (n'+1) sum into Fin n' plus the last index
    rw [Fin.sum_univ_castSucc]

    -- or equivalent theorem depending on imports

    -- use IH on the low n' bits
    specialize IHn' (v.extractLsb' 0 n')
    simp at *
    rw [IHn']

    sorry


theorem sum_eq_cpop : ∀ (u : UInt64) ,
    BitVec.ofNat 64 (∑ x : Fin 64, u.toBitVec[x].toNat) = u.toBitVec.cpop := by
  -- very slow, thats why i commented it. Searching for a lighter proof
  -- intros u
  -- simp
  -- unfold Finset.sum BitVec.cpop
  -- simp
  -- grind
  sorry


mkAll RV64 Instr execute
  PANIC:
  {
    syntax : PANIC,
    semantics: fun ms => (MState.setTerminated ms true),
    specification: True
  }
  LoadImmediate:
  {
    syntax : li (a:register), (m:immediate),
    semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
    specification:  ⦃P ⟦x[a] ← m; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadAddress:
  {
    syntax : la (a:register), (m:immediate),
    semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
    specification:  ⦃P ⟦x[a] ← m; pc++⟧ ∧ ¬⸨terminated⸩⦄
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
  rotr32:
  { syntax : rotr32 (dst:register) (r:register) (amt:immediate),
    semantics: fun ms => (ms.addRegisterAt dst (sext32 (rotr32 (lo32 (ms.getRegisterAt r))
                          (amt.toUInt32)))).incPc,
    specification:
      ⦃P ⟦x[dst] ← sext32 (rotr32 (lo32 x[r]) (lo32 (amt))) ; pc++⟧ ∧ ¬⸨terminated⸩⦄
      pc ↦ ⟨{pc+1} | {n : UInt64 | n ≠ pc + 1}⟩
      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  Sha256Sig0:
  { syntax : sha256sig0 (rs1:register) (rd:register),
    semantics: fun ms => (ms.applySig0 rd rs1).incPc,
    specification:
      ⦃P ⟦x[rd] ← sext32 (σ₀ (lo32 x[rs1])) ; pc++⟧ ∧ ¬⸨terminated⸩⦄
      pc ↦ ⟨{pc+1} | {n : UInt64 | n ≠ pc + 1}⟩
      ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  CountSetBits:
  {
    syntax: cpop (rd:register), (rs:register),
    semantics: fun ms => (ms.addRegisterAt rd (UInt64.ofBitVec
                          ((ms.getRegisterAt rs).toBitVec.cpop))).incPc,
    specification:
      ⦃P ⟦x[rd] ← UInt64.ofNat (∑ i : Fin 64, ((x[rs]).toBitVec[i]).toNat) ; pc++⟧ ∧ ¬⸨terminated⸩⦄
      pc ↦ ⟨{pc+1} | {n : UInt64 | n ≠ pc + 1}⟩
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
    specification:  ⦃P ⟦pc ← newPc⟧ ∧ labels[lbl] = some newPc ∧ x[r] = 0 ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{newPc} | {n : ProgramCounter | n ≠ newPc}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
                    ||
                    ⦃P ⟦pc++⟧ ∧ x[r] ≠ 0 ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }


theorem sum_eq_cpop' : ∀ (s : MState Instr) (rs : RegisterName) ,
  UInt64.ofNat (∑ x : Fin 64, (s.getRegisterAt rs).toBitVec[↑x].toNat) =
    { toBitVec := (s.getRegisterAt rs).toBitVec.cpop } := by
  intros ms rs
  simp only [UInt64.ofNat]
  rw [sum_eq_cpop]





def MState.runOneStep (ms : MState Instr) :=
  execute ms (ms.getCurrInstr)

def MState.runNSteps (ms : MState Instr) (n : Nat) :=
  match n with
  | 0 => ms
  | n' + 1 => MState.runNSteps (ms.runOneStep) n'

instance instRunnable : Runnable (MState Instr) where
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
P : Assertion<
pc dst addr : UInt64
L : Set UInt64
⊢ L = {n | n ≠ pc + 1} →
  hoare_triple_up_1 (fun st => P (st.incPc.addRegister dst addr) ∧ ¬st.terminated = true)
    (fun st => P st ∧ ¬st.terminated = true) pc {pc + 1} L (Instr.LoadAddress dst addr)

-/

def a := RV64["LoadImmediate"].get!.proof? = (POption.some (by
  sorry
  ))


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



example : specification_Sha256Sig0 := by
  unfold specification_Sha256Sig0
  intros P pc rs1 rd h_inter h_neq s curr getPc
  rintro ⟨pre, h_terminated⟩
  simp at curr
  simp at getPc
  simp at h_terminated
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
    have : (s.applySig0 rd rs1).incPc.pc = pc + 1 := by
      . unfold MState.applySig0 MState.addRegisterAt
        by_cases h: rd.nr == 0 <;> (simp [h] ; unfold MState.incPc ; rw [h_terminated] ; simp ; exact getPc)
    rw  [this]
  . intros n' hn'
    intros hneq
    rw [hneq] at hn'
    contradiction
  . constructor
    constructor
    . unfold MState.runOneStep execute
      rw [h_terminated, curr]
      simp
      unfold MState.applySig0
      have : (s.addRegisterAt rd (sext32 (σ₀ (lo32 (s.getRegisterAt rs1))))).incPc
                = (s.incPc.addRegisterAt rd (sext32 (σ₀ (lo32 (s.incPc.getRegisterAt rs1))))) := by
          unfold MState.addRegisterAt MState.incPc
          rw [h_terminated]
          by_cases d: rd.nr = 0 <;> simp [d]
          exact h_terminated
          unfold MState.getRegisterAt
          simp
      rw [this]
      exact pre
    . unfold MState.runOneStep execute
      rw [h_terminated, curr]
      simp
      unfold MState.applySig0 MState.addRegisterAt
      by_cases h: rd.nr == 0 <;> (simp [h] ; unfold MState.incPc ; rw [h_terminated])
    . unfold MState.runOneStep execute
      rw [h_terminated, curr]
      simp
      unfold MState.applySig0 MState.addRegisterAt
      by_cases h : rd.nr == 0 <;> (simp [h] ; unfold MState.incPc ; simp ; exact getPc )



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
        rw [Runnable_runNStep_eq_mstate_runNStep, runNSteps_1_eq_runOneStep]
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

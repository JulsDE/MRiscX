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



def a : UInt64 := 1
#eval a.shiftLeft 1
#eval a.shiftRight 1
#eval a >>> 1
#eval a <<< 1
#eval a.toBitVec.sshiftRight 1

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
    syntax : la (rd:register), (m:immediate),
    semantics: fun ms => (MState.addRegisterAt ms rd m).incPc,
    specification:  ⦃P ⟦x[rd] ← m; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  CopyRegister:
  {
    syntax: mv (rd:register), (rs:register),
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.getRegisterAt ms rs)),
    specification: ⦃P ⟦x[rd] ← x[rs] ; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  SubImmediate:
  {
    syntax: subi (rd:register), (rs:register), (imm:immediate),
    semantics: fun ms => (MState.addRegisterAt ms rd ((MState.getRegisterAt ms rs) - imm)).incPc,
    specification: ⦃P ⟦x[rd] ← x[rs] - imm; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  AddImmediate:
  {
    syntax: addi (rd:register), (rs:register), (imm:immediate),
    semantics: fun ms => (MState.addRegisterAt ms rd ((MState.getRegisterAt ms rs) + imm)).incPc,
    specification: ⦃P ⟦x[rd] ← x[rs] + imm; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  Add:
  {
    syntax: add (rd:register), (rs1:register), (rs2:register),
    semantics: fun ms => (MState.addRegisterAt ms rd ((MState.getRegisterAt ms rs1) +
                          (MState.getRegisterAt ms rs2))).incPc,
    specification: ⦃P ⟦x[rd] ← x[rs1] + x[rs2]; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadByteUnsigned:
  {
    syntax: lbu (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadByte_unsigned ms (rs + off))),
    specification: ⦃P ⟦x[rd] ← (mem_ub[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadByteSigned:
  {
    syntax: lb (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadByte_signed ms rd)),
    specification: ⦃P ⟦x[rd] ← (mem_sb[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadWordUnsigned:
  {
    syntax: lwu (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadWord_unsigned ms rd)),
    specification: ⦃P ⟦x[rd] ← (mem_uw[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadWordSigned:
  {
    syntax: lw (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadWord_signed ms rd)),
    specification: ⦃P ⟦x[rd] ← (mem_sw[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }

  ShiftLeftImmediate:
  {
    syntax: slli (rd:register), (rs:register), (i:immediate),
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd ((MState.getRegisterAt ms rs).shiftLeft i)),
    specification: ⦃P ⟦x[rd] ← x[rs] <<< i; pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }

  ShiftRightImmediate:
  {
    syntax: srli (rd:register), (rs:register), (i:immediate),
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd ((MState.getRegisterAt ms rs).shiftRight i)),
    specification: ⦃P ⟦x[rd] ← x[rs] >>> i; pc++⟧ ∧ ¬⸨terminated⸩⦄
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
    syntax : beqz (r:register), (lbl:label),
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
  JumpEq:
  {
    syntax : beq (r1:register), (r2:register), (lbl:label),
    semantics: fun ms =>  if (MState.getRegisterAt ms r1 == MState.getRegisterAt ms r2) then
                            MState.jump ms lbl
                          else
                            MState.incPc ms
                          ,
    specification:  ⦃P ⟦pc ← newPc⟧ ∧ labels[lbl] = some newPc ∧ x[r1] = x[r2] ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{newPc} | {n : ProgramCounter | n ≠ newPc}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
                    ||
                    ⦃P ⟦pc++⟧ ∧ x[r1] ≠ x[r2] ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  JumpNeq:
  {
    syntax : bne (r1:register), (r2:register), (lbl:label),
    semantics: fun ms =>  if (MState.getRegisterAt ms r1 ≠ MState.getRegisterAt ms r2) then
                            MState.jump ms lbl
                          else
                            MState.incPc ms
                          ,
    specification:  ⦃P ⟦pc ← newPc⟧ ∧ labels[lbl] = some newPc ∧ x[r1] ≠ x[r2] ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{newPc} | {n : ProgramCounter | n ≠ newPc}⟩
                    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
                    ||
                    ⦃P ⟦pc++⟧ ∧ x[r1] = x[r2] ∧ ¬⸨terminated⸩⦄
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

@[simp]
theorem MState.idk (ms : MState Instr) (r : RegisterName) :
    { memory := ms.memory, registers := ms.registers, pc := ms.pc, code := ms.code,
        terminated := ms.terminated : MState Instr}.addRegisterAt r = ms.addRegisterAt r

      := by
      unfold MState.addRegisterAt
      simp


theorem ms_addRegiseter_pc_eq_pc : ∀ (ms : MState Instr) (r : RegisterName) (v : UInt64),
    (MState.addRegisterAt ms r v).pc = ms.pc := by
  unfold MState.addRegisterAt
  intros ms r v
  by_cases d: r.nr = 0 <;> simp [d]



/-
P : Assertion<
pc dst addr : UInt64
L : Set UInt64
⊢ L = {n | n ≠ pc + 1} →
  hoare_triple_up_1 (fun st => P (st.incPc.addRegister dst addr) ∧ ¬st.terminated = true)
    (fun st => P st ∧ ¬st.terminated = true) pc {pc + 1} L (Instr.LoadAddress dst addr)

-/

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
  intros P pc r1 r2 h_inter h_notEmpty ms curr h_getPc
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
        by_cases h : r1.nr = 0
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




theorem spec_j :
  specification_Jump := by
  unfold specification_Jump hoare_triple_up_1
  intros P pc lbl newPc h_inter h_L_w s curr get_pc pre
  sorry

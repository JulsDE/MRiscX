import MRiscX.ExtendParser.GenerateAll
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
-- import MRiscX.ExtendParser.GenerateInstrSpecification
import MRiscX.Hoare.HoareCore
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.BitVec
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

private theorem cpopNatRec_eq_acc_add_sum_getLsbD {w : Nat} (v : BitVec w) :
    ∀ (pos acc : Nat), v.cpopNatRec pos acc =
      acc + ∑ i : Fin pos, (v.getLsbD i).toNat := by
  intro pos
  induction pos with
  | zero =>
      intro acc
      simp [BitVec.cpopNatRec]
  | succ n ih =>
      intro acc
      rw [BitVec.cpopNatRec_succ]
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      simp [Nat.add_assoc, Nat.add_comm]

theorem sum_getLsbD_eq_cpopNatRec : ∀ (w : Nat) (v : BitVec w),
    (∑ i : Fin w, (v.getLsbD i).toNat) = v.cpopNatRec w 0 := by
  intro w v
  rw [cpopNatRec_eq_acc_add_sum_getLsbD v w 0]
  simp


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
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadByte_signed ms (rs + off))),
    specification: ⦃P ⟦x[rd] ← (mem_sb[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadWordUnsigned:
  {
    syntax: lwu (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadWord_unsigned ms (rs + off))),
    specification: ⦃P ⟦x[rd] ← (mem_uw[rs + off]); pc++⟧ ∧ ¬⸨terminated⸩⦄
                    pc ↦ ⟨{pc + 1} | {n : ProgramCounter | n ≠ pc + 1}⟩
                   ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  }
  LoadWordSigned:
  {
    syntax: lw (rd:register), (off:immediate)((rs:register)), -- rd = container of value, rs holds address
    semantics: fun ms => MState.incPc (MState.addRegisterAt ms rd (MState.loadWord_signed ms (rs + off))),
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


/-
theorem sum_eq_cpop : ∀ (u : UInt64) ,
    BitVec.ofNat 64 (∑ x : Fin 64, u.toBitVec[x].toNat) = u.toBitVec.cpop := by
-/

theorem sum_eq_cpop' : ∀ (s : MState Instr) (rs : RegisterName) ,
  UInt64.ofNat (∑ x : Fin 64, (s.getRegisterAt rs).toBitVec[↑x].toNat) =
    { toBitVec := (s.getRegisterAt rs).toBitVec.cpop } := by
  intros ms rs
  simp only [UInt64.ofNat]
  rw [sum_eq_cpop]


open scoped BigOperators

private theorem bitVec_ofNat_sum {w : Nat} {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → Nat) :
    BitVec.ofNat w (∑ i ∈ s, f i) = ∑ i ∈ s, BitVec.ofNat w (f i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, BitVec.ofNat_add, ih]

-- lemma cpopNatRec_eq_sum_range {w : Nat} (bv : BitVec w) :
--     bv.cpopNatRec w 0 =
--       ∑ i : Fin w, (bv.getLsbD i).toNat := by
--   induction w with
--   | zero =>
--       simp [BitVec.cpopNatRec]
--   | succ w ih =>
--       simp [BitVec.cpopNatRec]


-- theorem asdkjl :
--     ∀ (w : Nat) (bv : BitVec w),
--       bv.cpop = (∑ x : Fin w, bv[x].toNat) := by
--   intro w bv
--   simp [BitVec.cpop, cpopNatRec_eq_sum_range, Finset.sum_fin_eq_sum_range,
--     BitVec.getLsbD_eq_getElem]

theorem BitVec.cpop_eq_sum : ∀ (w : Nat) (bv : BitVec w),
    bv.cpop = (∑ x : Fin w, bv[x].toNat) := by
  intro w bv
  rw [BitVec.cpop]
  rw [← sum_getLsbD_eq_cpopNatRec w bv]
  rw [bitVec_ofNat_sum]
  change (∑ i : Fin w, BitVec.ofNat w (bv.getLsbD i).toNat) =
    BitVec.ofNat w (∑ x : Fin w, bv[x].toNat)
  rw [bitVec_ofNat_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp



def MState.runOneStep (ms : MState Instr) :=
  execute ms (ms.getCurrInstr)

def MState.runNSteps (ms : MState Instr) (n : Nat) :=
  match n with
  | 0 => ms
  | n' + 1 => MState.runNSteps (ms.runOneStep) n'

instance instRunnable : Runnable (MState Instr) where
  runOneStep := MState.runOneStep
  runNSteps := MState.runNSteps






theorem asdf (ms : MState Instr):
  TMap.get ms.registers { nr := 14, name := "a4" } =
  ms.loadByte_unsigned (TMap.get ms.registers { nr := 15, name := toString 15 }) →
  UInt64.ofNat (∑ x : Fin 64, (TMap.get ms.registers { nr := 14, name := "a4" }).toBitVec[↑x].toNat) =
  {
    toBitVec :=
      (BitVec.setWidth 64 (TMap.get ms.memory
        (TMap.get ms.registers { nr := 15, name := toString 15 }))).cpop }
  := by
  intro h
  rw [h]
  unfold MState.loadByte_unsigned MState.loadByte_raw
  simp only [UInt64.ofNat]
  rw [sum_eq_cpop]

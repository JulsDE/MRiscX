import MRiscX.AbstractSyntax.Map

import Lean
open Lean Nat


def MRISCX_REG_SIZE : UInt64 := 32

abbrev RegisterNr := Fin (MRISCX_REG_SIZE.toNat)

namespace RegisterNr
  def bareNames :=
      [
        "x0",
        "x1",
        "x2",
        "x3",
        "x4",
        "x5",
        "x6",
        "x7",
        "x8",
        "x9",
        "x10",
        "x11",
        "x12",
        "x13",
        "x14",
        "x15",
        "x16",
        "x17",
        "x18",
        "x19",
        "x20",
        "x21",
        "x22",
        "x23",
        "x24",
        "x25",
        "x26",
        "x27",
        "x28",
        "x29",
        "x30",
        "x31"
        ]

    def abiNames :=
      [
        "zero",
        "ra",
        "sp",
        "gp",
        "tp",
        "t0",
        "t1",
        "t2",
        "s0",
        "s1",
        "a0",
        "a1",
        "a2",
        "a3",
        "a4",
        "a5",
        "a6",
        "a7",
        "s2",
        "s3",
        "s4",
        "s5",
        "s6",
        "s7",
        "s8",
        "s9",
        "s10",
        "s11",
        "t3",
        "t4",
        "t5",
        "t6"
      ]
  def isAbiName (str : String) :=
    if RegisterNr.abiNames.contains str || str == "fp" then
      true
    else
      false


  def isBareName (str : String) :=
    if RegisterNr.bareNames.contains str then
      true
    else
      false



  def ofNat (n:Nat) : RegisterNr := Fin.mk (n % MRISCX_REG_SIZE.toNat)
                        (by
                          apply Nat.mod_lt
                          unfold MRISCX_REG_SIZE
                          simp)
  def ofUInt64 (n:UInt64) : RegisterNr := Fin.mk (n.toNat % MRISCX_REG_SIZE.toNat)
                            (by
                              apply Nat.mod_lt
                              unfold MRISCX_REG_SIZE
                              simp)

  def toUInt64 (r : RegisterNr) : UInt64 := UInt64.ofNat r.toNat

  instance InstRegisterNrOfNat (n : Nat) : OfNat RegisterNr n where
    ofNat := RegisterNr.ofNat n

  def ofAbi? (str : String) : Option RegisterNr :=
    if str == "fp" then some (RegisterNr.ofNat 8)
    else if isAbiName str then
      some (RegisterNr.ofNat (RegisterNr.abiNames.idxOf str))
    else none

  def ofAbi! (str : String) (d : RegisterNr) : RegisterNr :=
    match ofAbi? str with
    | none => d
    | some r => r

end RegisterNr


structure RegisterName where
  nr : RegisterNr
  name : String
-- deriving DecidableEq
deriving Repr

def DefaultRegisterName := {nr := RegisterNr.ofNat 0, name := "zero" : RegisterName}

instance : Inhabited RegisterName where
  default := DefaultRegisterName



namespace RegisterName


  def beq (n₁ n₂ : RegisterName) := n₁.nr == n₂.nr

  def ofAbi? (str : String) : Option RegisterName :=
    match RegisterNr.ofAbi? str with
    | none => none
    | some r => RegisterName.mk r str

  def ofAbi! (str : String) (d : RegisterName) :=
    match ofAbi? str with
    | none => d
    | some n => n

  def ofAbi!_zero (str : String) :=
    match ofAbi? str with
    | some n => n
    | none => RegisterName.mk (RegisterNr.ofNat 0) ""
  -- def beq_regNr (n₁ n₂ : RegisterName) := n₁.nr  == n₂.nr


end RegisterName


instance : BEq RegisterName where
  beq n1 n2 := RegisterName.beq n1 n2


/--
In this type, only the RegisterNr matters. The name is only for delaboration.
This is why we need this axiom to be able to implement the LawfulBEq typeclass
-/
axiom register_name_equality : ∀ (n₁ n₂ : RegisterName),
  n₁.nr = n₂.nr → n₁ = n₂


instance: LawfulBEq RegisterName where
  rfl := by
    intros r
    unfold BEq.beq
    unfold instBEqRegisterName
    simp [RegisterName.beq]
  eq_of_beq := by
    intros a b h
    unfold BEq.beq instBEqRegisterName RegisterName.beq at h
    simp at h
    apply register_name_equality
    exact h

@[simp]
theorem RegisterName.register_eq_on_nr : ∀ (nr1 nr2 : RegisterNr) (str1 str2 : String),
  nr1 = nr2 →
  ({nr := nr1, name := str1} : RegisterName) = {nr := nr2, name := str2} := by
  intros nr1 nr2 str1 str2 h
  apply register_name_equality
  simp [h]

@[simp]
theorem RegisterName.register_eq_on_nr' : ∀ (nr : RegisterNr) (str1 str2 : String),
  ({nr := nr, name := str1} : RegisterName) = {nr := nr, name := str2} := by
  intros nr str1 str2
  apply register_name_equality
  simp



instance: ToString RegisterName where
   toString n := n.name



/--
Definiton of the registers
R := {r_1 ↦ w_1, … , r_k ↦ w_k}
-/
abbrev Registers := TMap RegisterName UInt64
  -- deriving Repr

def Registers.getByRegNr (regs : Registers) (nr : RegisterNr) :=
  match regs with
  | TMap.empty d => d
  | TMap.put k v t =>
    if k.nr == nr then
      v
    else
      Registers.getByRegNr t nr


@[simp]
theorem tReg_update_eq : ∀ (name : RegisterName) (nr : RegisterNr) (r t : Registers)
    (v : UInt64),
  name.nr = nr →
  r = (name ↦ v ; t) →
  r.getByRegNr nr = v
  := by
  intros name nr r t v h₁ h₂
  unfold Registers.getByRegNr
  simp
  rw [h₂]
  simp
  rw [h₁]
  simp

@[simp]
theorem tReg_update_neq : ∀ (name : RegisterName) (nr : RegisterNr) (r t : Registers)
    (v : UInt64),
  name.nr ≠ nr →
  r = (name ↦ v ; t) →
  r.getByRegNr nr = t.getByRegNr nr
  := by
  intros name nr r t v h₁ h₂
  unfold Registers.getByRegNr
  simp
  rw [h₂]
  simp [h₁]
  conv =>
    lhs
    unfold Registers.getByRegNr
    simp

example: ∀ (u : UInt64),
  (u.toNat).toUInt64 = u := by
  intros u
  simp

theorem UInt64.same_nat_mod_same_eq_same : ∀ (u m r : UInt64) (n v : Nat),
  r.toNat = v →
  m.toNat = n →
  u % m = r →
  (u.toNat % n) = v := by
  intros u m r n v h1 h2 h3
  rw [←h1, ←h2]
  rw [←UInt64.toNat_mod]
  rw [UInt64.toNat_inj]
  exact h3

theorem UInt64.same_nat_mod_same_neq_same : ∀ (u m r : UInt64) (n v : Nat),
  r.toNat = v →
  m.toNat = n →
  u % m ≠ r →
  (u.toNat % n) ≠ v := by
  intros u m r n v h1 h2 h3
  rw [←h1, ←h2]
  rw [←UInt64.toNat_mod]
  intros neq
  rw [UInt64.toNat_inj] at neq
  contradiction


@[simp]
theorem register_nr_symm (name1 name2 : RegisterName) (nr : RegisterNr) :
  name1.nr = nr →
  name1 = name2 →
  name2.nr = nr := by
  intros h_nr h_eq
  rw [←h_nr]
  rw [h_eq]


@[simp]
theorem n_not_zero_registerNr_not_zero : ∀ (n : UInt64),
  n % MRISCX_REG_SIZE ≠ 0 →
  RegisterNr.ofUInt64 n ≠ 0 := by
  intros n H
  unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE
  unfold MRISCX_REG_SIZE at H
  simp at *
  intros neq
  apply UInt64.same_nat_mod_same_neq_same <;> try assumption
  repeat simp

/--
RegisterMap with default value 0

R := {r_1 ↦ w_1, … , r_k ↦ w_k ; 0}
-/
def EmptyRegisters : Registers := TMap.empty 0

#check RegisterName.mk 1 ""

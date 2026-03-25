abbrev RegisterNr := Fin 32

def RegisterNr.ofNat (n:Nat) : RegisterNr := Fin.mk (n % 32) (by apply Nat.mod_lt;simp)
def RegisterNr.ofUInt64 (n:UInt64) : RegisterNr := Fin.mk (n.toNat % 32) (by apply Nat.mod_lt;simp)


structure RegisterName where
  nr : RegisterNr
  name : String
-- deriving DecidableEq

namespace RegisterName

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
      "fp",
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

  def beq (n₁ n₂ : RegisterName) := n₁.nr == n₂.nr

  -- def beq_regNr (n₁ n₂ : RegisterName) := n₁.nr  == n₂.nr

  def isAbiName (str : String) :=
    if abiNames.contains str then
      true
    else
      false


  def isBareName (str : String) :=
    if bareNames.contains str then
      true
    else
      false

end RegisterName

instance: BEq RegisterName where
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

instance: ToString RegisterName where
   toString n := n.name

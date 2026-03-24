
inductive RegisterNr where
  | zero
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | ten
  | eleven
  | twelve
  | thirteen
  | fourteen
  | fifteen
  | sixteen
  | seventeen
  | eighteen
  | nineteen
  | twenty
  | twentyone
  | twentytwo
  | twentythree
  | twentyfour
  | twentyfive
  | twentysix
  | twentyseven
  | twentyeight
  | twentynine
  | thirty
  | thirtyone
  | var : UInt64 → RegisterNr
deriving DecidableEq

namespace RegisterNr

def ofNat? (n : Nat) : Option RegisterNr :=
  match n with
  | 0 => some zero
  | 1 => some one
  | 2 => some two
  | 3 => some three
  | 4 => some four
  | 5 => some five
  | 6 => some six
  | 7 => some seven
  | 8 => some eight
  | 9 => some nine
  | 10 => some ten
  | 11 => some eleven
  | 12 => some twelve
  | 13 => some thirteen
  | 14 => some fourteen
  | 15 => some fifteen
  | 16 => some sixteen
  | 17 => some seventeen
  | 18 => some eighteen
  | 19 => some nineteen
  | 20 => some twenty
  | 21 => some twentyone
  | 22 => some twentytwo
  | 23 => some twentythree
  | 24 => some twentyfour
  | 25 => some twentyfive
  | 26 => some twentysix
  | 27 => some twentyseven
  | 28 => some twentyeight
  | 29 => some twentynine
  | 30 => some thirty
  | 31 => some thirtyone
  | _ => none

def ofNat! (n : Nat) (d : RegisterNr) : RegisterNr :=
  match n with
  | 0 => zero
  | 1 => one
  | 2 => two
  | 3 => three
  | 4 => four
  | 5 => five
  | 6 => six
  | 7 => seven
  | 8 => eight
  | 9 => nine
  | 10 => ten
  | 11 => eleven
  | 12 => twelve
  | 13 => thirteen
  | 14 => fourteen
  | 15 => fifteen
  | 16 => sixteen
  | 17 => seventeen
  | 18 => eighteen
  | 19 => nineteen
  | 20 => twenty
  | 21 => twentyone
  | 22 => twentytwo
  | 23 => twentythree
  | 24 => twentyfour
  | 25 => twentyfive
  | 26 => twentysix
  | 27 => twentyseven
  | 28 => twentyeight
  | 29 => twentynine
  | 30 => thirty
  | 31 => thirtyone
  | _ => d

def ofNat (n : Nat) : RegisterNr :=
  match n with
  | 0 => zero
  | 1 => one
  | 2 => two
  | 3 => three
  | 4 => four
  | 5 => five
  | 6 => six
  | 7 => seven
  | 8 => eight
  | 9 => nine
  | 10 => ten
  | 11 => eleven
  | 12 => twelve
  | 13 => thirteen
  | 14 => fourteen
  | 15 => fifteen
  | 16 => sixteen
  | 17 => seventeen
  | 18 => eighteen
  | 19 => nineteen
  | 20 => twenty
  | 21 => twentyone
  | 22 => twentytwo
  | 23 => twentythree
  | 24 => twentyfour
  | 25 => twentyfive
  | 26 => twentysix
  | 27 => twentyseven
  | 28 => twentyeight
  | 29 => twentynine
  | 30 => thirty
  | 31 => thirtyone
  | _ => var (UInt64.ofNat n)

def toNat
  | zero => 0
  | one => 1
  | two => 2
  | three => 3
  | four => 4
  | five => 5
  | six => 6
  | seven => 7
  | eight => 8
  | nine => 9
  | ten => 10
  | eleven => 11
  | twelve => 12
  | thirteen => 13
  | fourteen => 14
  | fifteen => 15
  | sixteen => 16
  | seventeen => 17
  | eighteen => 18
  | nineteen => 19
  | twenty => 20
  | twentyone => 21
  | twentytwo => 22
  | twentythree => 23
  | twentyfour => 24
  | twentyfive => 25
  | twentysix => 26
  | twentyseven => 27
  | twentyeight => 28
  | twentynine => 29
  | thirty => 30
  | thirtyone => 31
  | var u => u.toNat

def ofUInt64 (n : UInt64) : RegisterNr := ofNat n.toNat

instance : ToString RegisterNr where
  toString (nr) :=
  s!"{nr.toNat}"


  def eq (r1 r2 : RegisterNr) := (r1 == r2)

end RegisterNr

instance: BEq RegisterNr where
  beq r1 r2 := r1 == r2


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


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
deriving DecidableEq

namespace RegisterNr

def ofNat? (n : Nat) : Option RegisterNr :=
  match n with
  | 0 => some RegisterNr.zero
  | 1 => some RegisterNr.one
  | 2 => some RegisterNr.two
  | 3 => some RegisterNr.three
  | 4 => some RegisterNr.four
  | 5 => some RegisterNr.five
  | 6 => some RegisterNr.six
  | 7 => some RegisterNr.seven
  | 8 => some RegisterNr.eight
  | 9 => some RegisterNr.nine
  | 10 => some RegisterNr.ten
  | 11 => some RegisterNr.eleven
  | 12 => some RegisterNr.twelve
  | 13 => some RegisterNr.thirteen
  | 14 => some RegisterNr.fourteen
  | 15 => some RegisterNr.fifteen
  | 16 => some RegisterNr.sixteen
  | 17 => some RegisterNr.seventeen
  | 18 => some RegisterNr.eighteen
  | 19 => some RegisterNr.nineteen
  | 20 => some RegisterNr.twenty
  | 21 => some RegisterNr.twentyone
  | 22 => some RegisterNr.twentytwo
  | 23 => some RegisterNr.twentythree
  | 24 => some RegisterNr.twentyfour
  | 25 => some RegisterNr.twentyfive
  | 26 => some RegisterNr.twentysix
  | 27 => some RegisterNr.twentyseven
  | 28 => some RegisterNr.twentyeight
  | 29 => some RegisterNr.twentynine
  | 30 => some RegisterNr.thirty
  | 31 => some RegisterNr.thirtyone
  | _ => none

def ofNat! (n : Nat) (d : RegisterNr) : RegisterNr :=
  match n with
  | 0 => RegisterNr.zero
  | 1 => RegisterNr.one
  | 2 => RegisterNr.two
  | 3 => RegisterNr.three
  | 4 => RegisterNr.four
  | 5 => RegisterNr.five
  | 6 => RegisterNr.six
  | 7 => RegisterNr.seven
  | 8 => RegisterNr.eight
  | 9 => RegisterNr.nine
  | 10 => RegisterNr.ten
  | 11 => RegisterNr.eleven
  | 12 => RegisterNr.twelve
  | 13 => RegisterNr.thirteen
  | 14 => RegisterNr.fourteen
  | 15 => RegisterNr.fifteen
  | 16 => RegisterNr.sixteen
  | 17 => RegisterNr.seventeen
  | 18 => RegisterNr.eighteen
  | 19 => RegisterNr.nineteen
  | 20 => RegisterNr.twenty
  | 21 => RegisterNr.twentyone
  | 22 => RegisterNr.twentytwo
  | 23 => RegisterNr.twentythree
  | 24 => RegisterNr.twentyfour
  | 25 => RegisterNr.twentyfive
  | 26 => RegisterNr.twentysix
  | 27 => RegisterNr.twentyseven
  | 28 => RegisterNr.twentyeight
  | 29 => RegisterNr.twentynine
  | 30 => RegisterNr.thirty
  | 31 => RegisterNr.thirtyone
  | _ => d

instance : ToString RegisterNr where
  toString
  | RegisterNr.zero => "0"
  | RegisterNr.one => "1"
  | RegisterNr.two => "2"
  | RegisterNr.three => "3"
  | RegisterNr.four => "4"
  | RegisterNr.five => "5"
  | RegisterNr.six => "6"
  | RegisterNr.seven => "7"
  | RegisterNr.eight => "8"
  | RegisterNr.nine => "9"
  | RegisterNr.ten => "10"
  | RegisterNr.eleven => "11"
  | RegisterNr.twelve => "12"
  | RegisterNr.thirteen => "13"
  | RegisterNr.fourteen => "14"
  | RegisterNr.fifteen => "15"
  | RegisterNr.sixteen => "16"
  | RegisterNr.seventeen => "17"
  | RegisterNr.eighteen => "18"
  | RegisterNr.nineteen => "19"
  | RegisterNr.twenty => "20"
  | RegisterNr.twentyone => "21"
  | RegisterNr.twentytwo => "22"
  | RegisterNr.twentythree => "23"
  | RegisterNr.twentyfour => "24"
  | RegisterNr.twentyfive => "25"
  | RegisterNr.twentysix => "26"
  | RegisterNr.twentyseven => "27"
  | RegisterNr.twentyeight => "28"
  | RegisterNr.twentynine => "29"
  | RegisterNr.thirty => "30"
  | RegisterNr.thirtyone => "31"

  def eq (r1 r2 : RegisterNr) := (r1 == r2)

end RegisterNr

instance: BEq RegisterNr where
  beq r1 r2 := r1 == r2


structure RegisterName where
  nr : RegisterNr
  name : String
deriving DecidableEq

namespace RegisterName

  def beq (n₁ n₂ : RegisterName) := n₁ == n₂

  def beq_regNr (n₁ n₂ : RegisterName) := n₁.nr  == n₂.nr

end RegisterName

instance: BEq RegisterName where
  beq n1 n2 := RegisterName.beq n1 n2

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
    rw [h]

instance: ToString RegisterName where
   toString n := n.name

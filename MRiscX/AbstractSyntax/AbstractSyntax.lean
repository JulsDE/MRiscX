import MRiscX.AbstractSyntax.Map
import MRiscX.AbstractSyntax.Instr
import MRiscX.Parser.AssemblySyntax
import Lean
open Nat
open Lean Lean.Elab
/--
Purpose of this file:
This file establishes the syntax of the MRiscX assembly language, encompassing the definition
of instructions, labels, registers, memory and machine states. Given that the instructionsMap,
labels, registers, and memory are represented as maps, it may be beneficial to review the contents
of the file Maps.lean beforehand.


Next we define some Datatypes for the map keys.
This is because it makes it easier to understand which
map is being processed.
Firstly a register, which will hold a value
-/

inductive Register where
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

namespace Register

def ofNat? (n : Nat) : Option Register :=
  match n with
  | 0 => some Register.zero
  | 1 => some Register.one
  | 2 => some Register.two
  | 3 => some Register.three
  | 4 => some Register.four
  | 5 => some Register.five
  | 6 => some Register.six
  | 7 => some Register.seven
  | 8 => some Register.eight
  | 9 => some Register.nine
  | 10 => some Register.ten
  | 11 => some Register.eleven
  | 12 => some Register.twelve
  | 13 => some Register.thirteen
  | 14 => some Register.fourteen
  | 15 => some Register.fifteen
  | 16 => some Register.sixteen
  | 17 => some Register.seventeen
  | 18 => some Register.eighteen
  | 19 => some Register.nineteen
  | 20 => some Register.twenty
  | 21 => some Register.twentyone
  | 22 => some Register.twentytwo
  | 23 => some Register.twentythree
  | 24 => some Register.twentyfour
  | 25 => some Register.twentyfive
  | 26 => some Register.twentysix
  | 27 => some Register.twentyseven
  | 28 => some Register.twentyeight
  | 29 => some Register.twentynine
  | 30 => some Register.thirty
  | 31 => some Register.thirtyone
  | _ => none

def ofNat! (n : Nat) (d : Register) : Register :=
  match n with
  | 0 => Register.zero
  | 1 => Register.one
  | 2 => Register.two
  | 3 => Register.three
  | 4 => Register.four
  | 5 => Register.five
  | 6 => Register.six
  | 7 => Register.seven
  | 8 => Register.eight
  | 9 => Register.nine
  | 10 => Register.ten
  | 11 => Register.eleven
  | 12 => Register.twelve
  | 13 => Register.thirteen
  | 14 => Register.fourteen
  | 15 => Register.fifteen
  | 16 => Register.sixteen
  | 17 => Register.seventeen
  | 18 => Register.eighteen
  | 19 => Register.nineteen
  | 20 => Register.twenty
  | 21 => Register.twentyone
  | 22 => Register.twentytwo
  | 23 => Register.twentythree
  | 24 => Register.twentyfour
  | 25 => Register.twentyfive
  | 26 => Register.twentysix
  | 27 => Register.twentyseven
  | 28 => Register.twentyeight
  | 29 => Register.twentynine
  | 30 => Register.thirty
  | 31 => Register.thirtyone
  | _ => d

instance : ToString Register where
  toString
  | Register.zero => "0"
  | Register.one => "1"
  | Register.two => "2"
  | Register.three => "3"
  | Register.four => "4"
  | Register.five => "5"
  | Register.six => "6"
  | Register.seven => "7"
  | Register.eight => "8"
  | Register.nine => "9"
  | Register.ten => "10"
  | Register.eleven => "11"
  | Register.twelve => "12"
  | Register.thirteen => "13"
  | Register.fourteen => "14"
  | Register.fifteen => "15"
  | Register.sixteen => "16"
  | Register.seventeen => "17"
  | Register.eighteen => "18"
  | Register.nineteen => "19"
  | Register.twenty => "20"
  | Register.twentyone => "21"
  | Register.twentytwo => "22"
  | Register.twentythree => "23"
  | Register.twentyfour => "24"
  | Register.twentyfive => "25"
  | Register.twentysix => "26"
  | Register.twentyseven => "27"
  | Register.twentyeight => "28"
  | Register.twentynine => "29"
  | Register.thirty => "30"
  | Register.thirtyone => "31"

end Register



-- instance: Coe Register UInt64 where
--  coe c := (Register.ofNat?)


/--
Next, the memory address. This address will point to a certain
address in the memory which holds some value
-/
abbrev MemoryAddress := UInt64

/--
The InstructionIndex is a serial number which points
to a instruction in the stack
-/
abbrev InstructionIndex := UInt64

abbrev ProgramCounter := UInt64

/--
A total map which holds the instructions of a program
tied to a unsigned 64-bit integers as InstructionIndex. The default value of this map
is the instruction Instr.Panic.

IM := {uint64_1 ↦ instr_1, uint64_2 ↦ instr_2, ..., uint64_n ↦ instr_n}
/ default:  Instr.IPanic
-/
def InstructionMap := TMap InstructionIndex Instr
deriving Repr, Inhabited

instance : ToString InstructionMap where
  toString (instrMap : InstructionMap) := reprStr instrMap

/--
Empty InstructionMap which serves as standard InstructionMap
-/
def EmptyInstructionMap : InstructionMap := TMap.empty Instr.Panic

/--
A partial map LabelMap, which holds all the Labels as key and links these
to an unsigned 64-bit integers.

LM := {l_1 ↦ uint64_1, l_2 ↦ uint64_2, ..., l_n ↦ uint64_n}
-/
def LabelMap := PMap String UInt64
deriving Repr, Inhabited

instance : ToString LabelMap where
  toString (labelMap : LabelMap) := reprStr labelMap


/--
Empty LabelMap which serves as standard LabelMap
-/
def EmptyLabels : LabelMap := PMap.empty


/--
The InstructionMap and the LabelMap are combined into a single structure,
which is refered as `Code`.
-/
structure Code where
  instructionMap: InstructionMap
  labels: LabelMap


/--
A default instance of Code, containing an empty `InstructionMap` and an empty `LabelMap`.
-/
def DefaultCode : Code := { instructionMap := EmptyInstructionMap, labels := EmptyLabels }



namespace Code
  def setCMap (m : Code) (c : InstructionMap) : Code :=
    { m with instructionMap := c}

  def setLabels (m : Code) (l : LabelMap) : Code :=
    { m with labels := l}

  def addMultipleLabels (m : Code) (l : List (String × UInt64)) : Code :=
  match l with
  | [] => m
  | h :: t => addMultipleLabels {m with labels := p(h.1 ↦ h.2 ; m.labels)} t

  def addCMap (m : Code) (id : InstructionIndex) (v : Instr) : Code :=
    {m with instructionMap := (id ↦ v ; m.instructionMap)}

  def addLabels (m : Code) (id : String) (v : UInt64) : Code :=
    {m with labels := p(id ↦ v ; m.labels)}

  def addMaps (m : Code) (id_c : InstructionIndex) (v_c : Instr) (id_l : String)
      (v_l : UInt64) : Code :=
    {m with instructionMap := (id_c ↦ v_c ; m.instructionMap), labels :=
    p(id_l ↦ v_l ; m.labels)}

  def setMaps (m : Code) (c : InstructionMap) (l : LabelMap) :=
    {m with instructionMap := c, labels := l}

  def getLabel (m : Code) (l : String): Option UInt64 := m.labels.get l

  def getInstrAt (m : Code) (l : UInt64): Instr := m.instructionMap.get l
end Code




/--
Definiton of the registers
R := {r_1 ↦ w_1, … , r_k ↦ w_k}
-/
def Registers := TMap Register UInt64
  -- deriving Repr

/--
RegisterMap with default value 0

R := {r_1 ↦ w_1, … , r_k ↦ w_k ; 0}
-/
def EmptyRegisters : Registers := TMap.empty 0

/--
Definiton of the memory
M := {m_1 ↦ w_1, … , m_k ↦ w_k}
-/
def Memory := TMap MemoryAddress UInt64
  deriving Repr


/--
MemoryMap with default value 0

M := {m_1 ↦ w_1, … , m_k ↦ w_k ; 0}
-/
def EmptyMemory : Memory := TMap.empty 0

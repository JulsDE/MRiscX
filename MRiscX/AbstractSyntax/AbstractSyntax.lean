import MRiscX.AbstractSyntax.Map
import MRiscX.AbstractSyntax.Instr
import MRiscX.Parser.AssemblySyntax
import Lean
open Nat
open Lean Lean.Elab
/-
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

namespace Register
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
end Register


abbrev Register := UInt64


instance: Coe Register UInt64 where
 coe c := (c:UInt64)


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
  deriving Repr

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

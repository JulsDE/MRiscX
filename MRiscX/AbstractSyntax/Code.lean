import MRiscX.AbstractSyntax.Registers
import MRiscX.AbstractSyntax.Memory
import MRiscX.AbstractSyntax.Instr
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

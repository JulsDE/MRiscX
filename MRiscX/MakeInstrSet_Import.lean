import MRiscX.AbstractSyntax.Map


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

/-
Everything is now brought together in a single structure called MState, which represents
the machine's MState This structure holds the memory, registers, the code, a program counter (PC),
and a termination flag. The program counter points to the next instruction to be executed,
while the termination flag indicates whether the machine state has halted or if further
evaluation should continue.
-/
structure MState where
  memory: Memory
  registers: Registers
  pc: ProgramCounter
--   code: Code
  terminated: Bool

/-
To perform the operations on the MState like we want to, we need to implement some
functions.
-/
namespace MState

  -- def currInstruction (ms:MState) : Instr :=
  --   ms.code.instructionMap.get (ms.pc)

  def incPc (ms:MState) : MState :=
    {ms with pc := ms.pc + 1}

  def setPc (ms:MState) (p:UInt64) : MState :=
    {ms with pc := p}

  def setRegister (ms:MState) (r:Registers) : MState :=
    {ms with registers := r}

  def addRegister (ms:MState) (i:UInt64) (v:UInt64): MState :=
    {ms with registers := (i ↦ v ; ms.registers)}

  def getRegisterAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.registers.get (i)

  def setMemory (ms:MState) (m:Memory) : MState :=
    {ms with memory := m}

  def addMemory (ms:MState) (i:UInt64) (v:UInt64) : MState :=
    {ms with memory := (i ↦ v ; ms.memory)}

  def getMemoryAt (ms:MState) (i:UInt64) : UInt64 :=
    ms.memory.get (i)


  /-
  This creates a Machine state with the pointer which the label [s] points to.
  If there is no label [s] in code.labels, terminated is set to true.
  -/
  def jump (ms:MState) (s:String) : MState := ms
    -- match ms.code.labels.get s with
    -- | some i => {ms with pc := i}
    -- | none => {ms with terminated := true}

  def setTerminated (ms : MState) (terminated : Boolean): MState := ms

end MState

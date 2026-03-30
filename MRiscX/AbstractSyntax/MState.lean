-- import MRiscX.AbstractSyntax.Code
import MRiscX.AbstractSyntax.Registers
import MRiscX.AbstractSyntax.Memory


abbrev ProgramCounter := UInt64

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

  terminated: Bool
  instrCounter : Nat

def DefaultMState : MState :=
  {registers := EmptyRegisters, memory := EmptyMemory, pc := 0,
    terminated := false, instrCounter := 0}

/-
To perform the operations on the MState like we want to, we need to implement some
functions.


Those function do not functions implemented here to avoid unfolding the functions and
have a better experience while simping in proofs. Might be refactored.
-/
namespace MState

  -- def currInstruction (ms:MState) (code : Code): Instr :=
  --   code.instructionMap.get (ms.pc)

  def incPc (ms:MState) : MState :=
    {ms with pc := ms.pc + 1}

  def setPc (ms:MState) (p:UInt64) : MState :=
    {ms with pc := p}

  def setRegister (ms:MState) (r:Registers) : MState :=
    {ms with registers := r}

  def addRegister (ms:MState) (i : RegisterName) (v:UInt64) : MState :=
    -- Register zero is always zero
    if i.nr == 0 then
      ms
    else
      {ms with registers := (i ↦ v ; ms.registers)}

  def getRegisterAt (ms:MState) (i : RegisterName) : UInt64 :=
    if i.nr == 0 then
      0
    else
      ms.registers.get i

  def getRegisterAtNr (ms:MState) (i : RegisterNr) : UInt64 :=
    ms.registers.getByRegNr i

  def setMemory (ms:MState) (m:Memory) : MState :=
    {ms with memory := m}

  def storeByte (ms : MState) (i : MemoryAddress) (v : Byte) : MState :=
    {ms with memory := (i ↦ v ; ms.memory)}

  def storeHalfword (ms : MState) (i : MemoryAddress) (v : Halfword) : MState :=
    let b0 := v.extractLsb' 0 8
    let b1 := v.extractLsb' 8 8
    {ms with memory :=  (i ↦ b0 ;
                        ((i + 1) ↦ b1 ;
                        ms.memory))}

  def storeWord (ms : MState) (v : Word) (i : MemoryAddress) : MState :=
    let b0 := v.extractLsb' 0 8
    let b1 := v.extractLsb' 8 8
    let b2 := v.extractLsb' 16 8
    let b3 := v.extractLsb' 24 8
    {ms with memory :=  (i ↦ b0 ;
                        ((i + 1) ↦ b1 ;
                        ((i + 2) ↦ b2 ;
                        ((i + 3) ↦ b3 ;
                        ms.memory))))}

  def storeDoubleword (ms : MState) (i : MemoryAddress) (v : Doubleword) : MState :=
    let b0 := v.extractLsb' 0 8
    let b1 := v.extractLsb' 8 8
    let b2 := v.extractLsb' 16 8
    let b3 := v.extractLsb' 24 8
    let b4 := v.extractLsb' 32 8
    let b5 := v.extractLsb' 40 8
    let b6 := v.extractLsb' 48 8
    let b7 := v.extractLsb' 56 8
    {ms with memory := (i ↦ b0 ;
                       ((i + 1) ↦ b1 ;
                       ((i + 2) ↦ b2 ;
                       ((i + 3) ↦ b3 ;
                       ((i + 4) ↦ b4 ;
                       ((i + 5) ↦ b5 ;
                       ((i + 6) ↦ b6 ;
                       ((i + 7) ↦ b7 ;
                        ms.memory))))))))}

  def loadByte  (ms : MState) (a : MemoryAddress) : Byte :=
    ms.memory.get a

  def loadHalfword (ms : MState) (addr : MemoryAddress) : Halfword :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    b1 ++ b0

  def loadWord (ms : MState) (addr : MemoryAddress) : Word :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    let b2 := ms.memory.get (addr + 2)
    let b3 := ms.memory.get (addr + 3)
    b3 ++ b2 ++ b1 ++ b0

  def loadDoubleword (ms : MState) (addr : MemoryAddress) : Doubleword :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    let b2 := ms.memory.get (addr + 2)
    let b3 := ms.memory.get (addr + 3)
    let b4 := ms.memory.get (addr + 4)
    let b5 := ms.memory.get (addr + 5)
    let b6 := ms.memory.get (addr + 6)
    let b7 := ms.memory.get (addr + 7)
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0


  def getMemoryAt (ms:MState) (i:MemoryAddress) : Byte :=
    ms.memory.get (i)

  -- def setInstructionMap (ms:MState) (sc:InstructionMap) : MState :=
  --   {ms with code.instructionMap := sc}

  -- def setCode (ms: MState) (code: Code) : MState :=
  --   {ms with code := code}

  -- def setLabels (ms:MState) (l:LabelMap) : MState :=
  --   {ms with code.labels := l}

  def setTerminated (ms:MState) (bool:Bool) : MState :=
    {ms with terminated := bool}

  def incInstrCounter (ms : MState) :=
    {ms with instrCounter := ms.instrCounter + 1}

  -- def getLabelAt (ms:MState) (s:String) : Option UInt64 :=
  --   ms.code.labels.get s

  -- def createStandardState (c : Code): MState :=
  --   {DefaultMState with code := c}

def LabelMap := PMap String UInt64
deriving Repr, Inhabited
  /-
  This creates a Machine state with the pointer which the label [s] points to.
  If there is no label [s] in code.labels, terminated is set to true.
  -/
  def jump (ms:MState) (labels: LabelMap) (s:String) : MState :=
    match labels.get s with
    | some i => {ms with pc := i}
    | none => {ms with terminated := true}


end MState

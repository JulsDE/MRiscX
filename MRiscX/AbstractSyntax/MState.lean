import MRiscX.AbstractSyntax.NewCode
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
structure MState (Instr : Type) where
  memory: Memory
  registers: Registers
  pc: ProgramCounter
  code: Code Instr
  terminated: Bool
  instrCounter : Nat

class MachineStateI (γ : Type)
    (InstrType CodeType RegisterNrType RegisterValType ProgramCounterType: Type) where
  getCode : γ → CodeType
  getLabelAt : γ → String → Option ProgramCounterType
  getTerminated : γ → Bool
  addRegister : γ → RegisterNrType → RegisterValType → γ
  getRegisterAt : γ → RegisterNrType → RegisterValType
  setPc : γ → ProgramCounterType → γ
  getPc : γ → ProgramCounterType
  currInstruction : γ → InstrType


class Runnable (α) where
  runOneStep: α → α
  runNSteps : α → Nat → α

/-
To perform the operations on the MState like we want to, we need to implement some
functions.


Those function do not functions implemented here to avoid unfolding the functions and
have a better experience while simping in proofs. Might be refactored.
-/
namespace MState
  variable {InstrType : Type} (ms : MState InstrType)
  -- def currInstruction (ms:MState) (code : Code): Instr :=
  --   code.instructionMap.get (ms.pc)

  def incPc :=
    {ms with pc := ms.pc + 1}

  def setPc (p:UInt64) : MState InstrType :=
    {ms with pc := p}

  def setRegister (r:Registers) : MState InstrType :=
    {ms with registers := r}

  def addRegisterAt (i : RegisterName) (v:UInt64) :=
    -- Register zero is always zero
    if i.nr == 0 then
      ms
    else
      {ms with registers := (i ↦ v ; ms.registers)}

  def getRegisterAt (i : RegisterName) : UInt64 :=
    if i.nr == 0 then
      0
    else
      ms.registers.get i

  def getRegisterAtNr (i : RegisterNr) : UInt64 :=
    ms.registers.getByRegNr i

  def setMemory (m:Memory) : MState InstrType :=
    {ms with memory := m}

  def storeByte (i : MemoryAddress) (v : Byte) : MState InstrType :=
    {ms with memory := (i ↦ v ; ms.memory)}

  def storeHalfword (i : MemoryAddress) (v : Halfword) : MState InstrType :=
    let b0 := v.extractLsb' 0 8
    let b1 := v.extractLsb' 8 8
    {ms with memory :=  (i ↦ b0 ;
                        ((i + 1) ↦ b1 ;
                        ms.memory))}

  def storeWord (v : Word) (i : MemoryAddress) : MState InstrType :=
    let b0 := v.extractLsb' 0 8
    let b1 := v.extractLsb' 8 8
    let b2 := v.extractLsb' 16 8
    let b3 := v.extractLsb' 24 8
    {ms with memory :=  (i ↦ b0 ;
                        ((i + 1) ↦ b1 ;
                        ((i + 2) ↦ b2 ;
                        ((i + 3) ↦ b3 ;
                        ms.memory))))}

  def storeDoubleword (i : MemoryAddress) (v : Doubleword) : MState InstrType :=
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

  def loadByte  (a : MemoryAddress) : Byte :=
    ms.memory.get a

  def loadHalfword (addr : MemoryAddress) : Halfword :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    b1 ++ b0

  def loadWord (addr : MemoryAddress) : Word :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    let b2 := ms.memory.get (addr + 2)
    let b3 := ms.memory.get (addr + 3)
    b3 ++ b2 ++ b1 ++ b0

  def loadDoubleword (ms : MState Instr) (addr : MemoryAddress) : Doubleword :=
    let b0 := ms.memory.get addr
    let b1 := ms.memory.get (addr + 1)
    let b2 := ms.memory.get (addr + 2)
    let b3 := ms.memory.get (addr + 3)
    let b4 := ms.memory.get (addr + 4)
    let b5 := ms.memory.get (addr + 5)
    let b6 := ms.memory.get (addr + 6)
    let b7 := ms.memory.get (addr + 7)
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0


  def getMemoryAt (i:MemoryAddress) : Byte :=
    ms.memory.get (i)

  -- def setInstructionMap (ms:MState Instr) (sc:InstructionMap) : MState Instr:=
  --   {ms with code.instructionMap := sc}

  -- def setCode (ms: MState Instr) (code: Code) : MState Instr:=
  --   {ms with code := code}

  -- def setLabels (ms:MState) (l:LabelMap) : MState :=
  --   {ms with code.labels := l}

  def setTerminated (bool:Bool) : MState InstrType :=
    {ms with terminated := bool}

  def incInstrCounter :=
    {ms with instrCounter := ms.instrCounter + 1}

  def getCode (ms : MState Instr) :=
    ms.code

  def getCurrInstr (ms : MState Instr) : Instr :=
    ms.code.instrMap.get ms.pc

  def getLabelAt (ms : MState Instr) (lbl : String) : Option ProgramCounter :=
    ms.getCode.labelMap.get lbl

  -- def getLabelAt (ms:MState Instr) (s:String) : Option UInt64 :=
  --   ms.code.labels.get s

  -- def createStandardState (c : Code): MState Instr:=
  --   {DefaultMState Instrwith code := c}

def LabelMap := PMap String UInt64
deriving Repr, Inhabited
  /-
  This creates a Machine state with the pointer which the label [s] points to.
 If there is no label [s] in code.labels, terminated is set to true.
  -/
  def jump (s:String) : MState InstrType :=
    match ms.code.labelMap.get s with
    | some i => {ms with pc := i}
    | none => {ms with terminated := true}




-- instance : MachineStateI (MState Instr) where
--   addRegister (ms:MState Instr) (r : RegisterName) (v : UInt64) := MState.addRegisterAt (ms) r v
--   setPc (ms : MState Instr) (newPc : ProgramCounter) := setPc ms newPc
end MState

instance instMState {Instr : Type} : MachineStateI (MState Instr) Instr (Code Instr) RegisterName UInt64
                                        ProgramCounter where
    currInstruction := MState.getCurrInstr
    getLabelAt := MState.getLabelAt
    getTerminated := MState.terminated
    getCode := MState.getCode
    addRegister := MState.addRegisterAt
    getRegisterAt := MState.getRegisterAt
    setPc := MState.setPc
    getPc := MState.pc

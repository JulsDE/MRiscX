import MRiscX.AbstractSyntax.MState

open Nat

/-
This file holds the functionality of the interpreter of the assembly language.
The function `runOneStep` evaluates each instruction and performs the desired action
on the abstract syntax.
-/

namespace MState

  -- small jump if function to have the runOneStep function cleaner
  def jif (ms: MState) (reg : RegisterName) (lbl : String) (cond : UInt64 → Bool) :=
      let regCont := ms.getRegisterAt reg
      if cond regCont then
        ms.jump lbl
      else
        ms.incPc

  -- small jump if function to have the runOneStep function cleaner
  def jif' (ms: MState) (reg1 reg2 : RegisterName) (lbl:String) (cond : UInt64 → UInt64 → Bool) :=
      let reg1Cont := ms.getRegisterAt reg1
      let reg2Cont := ms.getRegisterAt reg2
      if cond reg1Cont reg2Cont then
        ms.jump lbl
      else
        ms.incPc


  /--
  This function evaluates the given machine state to a new one.
  Tt represents the **nxt** function from the paper
  `LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
  In: International Conference on Software Engineering and Formal Methods.
  Cham: Springer International Publishing, 2020. S. 193-213.`

  Generally, if the `terminated` of the `State` is `false` and the instruction
  is legal and evaluateable, a new `State` is
  returned holding the next instructions and the updated storage.
  When the instruction is not legal (e.g. jmp s, there is no label `s`),
  `terminated` is set to `true`.
  -/
  def runOneStep (ms:MState) : MState :=
    if ms.terminated then ms
    else
      let instr := ms.currInstruction
      match instr with
      | Instr.LoadAddress (dst:RegisterName) (addr : UInt64) =>
        (ms.addRegister dst addr).incPc.incInstrCounter
      | Instr.LoadImmediate (dst) (i) =>
        (ms.addRegister dst i).incPc.incInstrCounter
      | Instr.LoadNegImmediate (dst) (i) =>
        let nr : UInt64 := 0 - i
        (ms.addRegister dst nr).incPc.incInstrCounter
      | Instr.CopyRegister (dst) (src) =>
        (ms.addRegister dst (ms.getRegisterAt src)).incPc.incInstrCounter
      | Instr.AddImmediate (dst) (reg) (i) =>
        (ms.addRegister dst ((ms.getRegisterAt reg) + i)).incPc.incInstrCounter
      | Instr.AddNegImmediate (dst) (reg) (i) =>
        (ms.addRegister dst ((ms.getRegisterAt reg) - i)).incPc.incInstrCounter
      | Instr.Increment (dst) =>
        (ms.addRegister dst (ms.getRegisterAt dst + 1)).incPc.incInstrCounter
      | Instr.AddRegister (dst) (reg1) (reg2) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1) + (ms.getRegisterAt reg2))).incPc.incInstrCounter
      | Instr.SubImmediate (dst) (reg) (i) =>
        (ms.addRegister dst ((ms.getRegisterAt reg) - i)).incPc.incInstrCounter
      | Instr.Decrement (dst) =>
        (ms.addRegister dst ((ms.getRegisterAt dst) - 1)).incPc.incInstrCounter
      | Instr.SubRegister (dst) (reg1) (reg2) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1) - (ms.getRegisterAt reg2))).incPc.incInstrCounter
      | Instr.XorImmediate (dst) (reg) (i) =>
        (ms.addRegister dst ((ms.getRegisterAt reg).xor i)).incPc.incInstrCounter
      | Instr.XOR (dst) (reg1) (reg2) =>
        (ms.addRegister dst ((ms.getRegisterAt reg1).xor (ms.getRegisterAt reg2))).incPc.incInstrCounter
      | Instr.LoadWordImmediate (dst) (addr) =>
        let content := UInt64.ofBitVec ((ms.loadWord (addr)).setWidth 64)
        (ms.addRegister dst (content)).incPc.incInstrCounter
      | Instr.LoadWordReg (dst) off (regWithAddr) =>
        let addr := ms.getRegisterAt regWithAddr
        let content := UInt64.ofBitVec ((ms.loadWord (addr + off)).setWidth 64)
        (ms.addRegister dst (content)).incPc.incInstrCounter
      | Instr.StoreWord (reg) off (dst) =>
        let regCont := (ms.getRegisterAt reg).toBitVec.extractLsb' 0 32
        let addr := (ms.getRegisterAt dst)
        (ms.storeWord (regCont) (addr + off))
        -- (ms.addMemory (ms.getRegisterAt dst) (ms.getRegisterAt reg)).incPc.incInstrCounter
      | Instr.Jump (lbl:String) =>
        ms.incInstrCounter.jump lbl
      | Instr.JumpEq (reg1) (reg2) (lbl:String) =>
        jif' ms.incInstrCounter reg1 reg2 lbl (fun n m => n == m)
      | Instr.JumpNeq (reg1) (reg2) (lbl:String) =>
        jif' ms.incInstrCounter reg1 reg2 lbl (fun n m => n != m)
      | Instr.JumpGt (reg1) (reg2) (lbl:String) =>
        jif' ms.incInstrCounter reg1 reg2 lbl (fun n m => n > m)
      | Instr.JumpLe (reg1) (reg2) (lbl:String) =>
        jif' ms.incInstrCounter reg1 reg2 lbl (fun n m => n <= m)
      | Instr.JumpEqZero (reg) (lbl:String) =>
        jif ms.incInstrCounter reg lbl (fun n => n == 0)
      | Instr.JumpNeqZero reg (lbl:String) =>
        jif ms.incInstrCounter reg lbl (fun n => n ≠ 0)
      | Instr.Panic => ms.setTerminated true
      -- | _ => ms.setTerminated true

  /--
  Runs `runOneStep` `n` times.
  It represents the function **nxt^n** from
  `LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
  In: International Conference on Software Engineering and Formal Methods.
  Cham: Springer International Publishing, 2020. S. 193-213.`
  -/
  def runNSteps (ms:MState) (n:Nat) : MState :=
    match n with
    | zero => ms
    | succ n' => ms.runOneStep.runNSteps n'


  def runUntilTerminatedWithFuel (ms : MState) (fuel : Nat) : MState :=
    match fuel with
    | Nat.zero => ms
    | Nat.succ n' =>
      if ms.terminated then
        ms
      else
        runUntilTerminatedWithFuel ms.runOneStep (n')

  def runUntilTerminated (ms : MState) : MState :=
    runUntilTerminatedWithFuel ms UInt64.size


  def nextInstruction (ms:MState) : Instr := ms.runOneStep.currInstruction

end MState

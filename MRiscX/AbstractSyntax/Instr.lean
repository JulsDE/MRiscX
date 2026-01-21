/-
Definition of the Instructions
-/
inductive Instr : Type where
  | LoadAddress       : UInt64 → UInt64 → Instr
  | LoadImmediate     : UInt64 → UInt64 → Instr
  | CopyRegister      : UInt64 → UInt64 → Instr
  | AddImmediate      : UInt64 → UInt64 → UInt64 → Instr
  | Increment         : UInt64 → Instr
  | AddRegister       : UInt64 → UInt64 → UInt64 → Instr
  | SubImmediate      : UInt64 → UInt64 → UInt64 → Instr
  | Decrement         : UInt64 → Instr
  | SubRegister       : UInt64 → UInt64 → UInt64 → Instr
  | XorImmediate      : UInt64 → UInt64 → UInt64 → Instr
  | XOR               : UInt64 → UInt64 → UInt64 → Instr
  | LoadWordImmediate : UInt64 → UInt64 → Instr
  | LoadWordReg       : UInt64 → UInt64 → Instr
  | StoreWord         : UInt64 → UInt64 → Instr
  | Jump              : String →  Instr
  | JumpEq            : UInt64 → UInt64 → String → Instr
  | JumpNeq           : UInt64 → UInt64 → String → Instr
  | JumpGt            : UInt64 → UInt64 → String → Instr
  | JumpLe            : UInt64 → UInt64 → String → Instr
  | JumpEqZero        : UInt64 → String → Instr
  | JumpNeqZero       : UInt64 → String → Instr
  | Panic             : Instr
  deriving Repr, BEq, Inhabited


/-
ToString for delaboration
-/
instance : ToString Instr where
  toString
    | Instr.LoadAddress dst addr =>
      let hex := addr.toBitVec.zeroExtend (Nat.log2 addr.toNat + 1)
      s!"la x{dst}, {hex}"
    | Instr.LoadImmediate dst i => s!"li x{dst}, {i}"
    | Instr.CopyRegister dst src => s!"mv x{dst} , x{src}"
    | Instr.AddImmediate dst reg i => s!"addi x{dst}, x{reg}, {i}"
    | Instr.Increment dst => s!"inc x{dst}"
    | Instr.AddRegister dst reg1 reg2 => s!"add x{dst}, x{reg1}, x{reg2}"
    | Instr.SubImmediate dst reg i => s!"subi x{dst}, x{reg}, {i}"
    | Instr.Decrement dst => s!"dec x{dst}"
    | Instr.SubRegister dst reg1 reg2 => s!"sub x{dst}, x{reg1}, x{reg2}"
    | Instr.XorImmediate dst reg i => s!"xori x{dst}, x{reg}, {i}"
    | Instr.XOR dst reg1 reg2 => s!"xor x{dst}, x{reg1}, x{reg2}"
    | Instr.LoadWordImmediate dst addr =>
      let hex := addr.toBitVec.zeroExtend (Nat.log2 addr.toNat + 1)
      s!"lw x{dst}, {hex}"
    | Instr.LoadWordReg dst addr => s!"lw x{dst}, x{addr}"
    | Instr.StoreWord reg dst => s!"sw x{reg}, x{dst}"
    | Instr.Jump lbl => s!"j {lbl}"
    | Instr.JumpEq reg1 reg2 lbl => s!"beq x{reg1}, x{reg2}, {lbl}"
    | Instr.JumpNeq reg1 reg2 lbl => s!"bne x{reg1}, x{reg2}, {lbl}"
    | Instr.JumpGt reg1 reg2 lbl => s!"bgt x{reg1}, x{reg2}, {lbl}"
    | Instr.JumpLe reg1 reg2 lbl => s!"ble x{reg1}, x{reg2}, {lbl}"
    | Instr.JumpEqZero reg lbl => s!"beqz x{reg}, {lbl}"
    | Instr.JumpNeqZero reg lbl => s!"bnez x{reg}, {lbl}"
    | Instr.Panic => "Panic!"

namespace Instr
  def beq (i j : Instr) : Bool :=
    match toString i, toString j with
    | s , s' => s == s'

  theorem refl : forall i : Instr,
    beq i i = true := by
    intros
    rewrite [beq]
    simp

end Instr

instance : BEq Instr where
  beq := Instr.beq

import MRiscX.AbstractSyntax.Registers
/--
Definition of the Instructions.
-/
inductive Instr : Type where
  /--
    Load an address into a register

    Syntax:

    `la x dst, m`

    where `(dst m : UInt64)`.

    Note: Numbers of type UInt64 can be written as hexadecimal
    (e.g. `0xf123`), which might serve as address.
  -/
  | LoadAddress       : RegisterName → UInt64 → Instr
  /--
    Load an immediate value into a register

    Syntax:

    `li x dst, m`

    where `(dst m : UInt64)`.
  -/
  | LoadImmediate     : RegisterName → UInt64 → Instr
  /--
    Load an immediate value into a register.

    Syntax:

    `la x dst, - val`

    where `(dst reg : UInt64)`.
  -/
  | LoadNegImmediate     : RegisterName → UInt64 → Instr
  /--
    Load a negative value in a register.

    Syntax:

    `mv x dst, x reg`

    where `(dst reg : UInt64)`.
  -/
  | CopyRegister      : RegisterName → RegisterName → Instr
  /--
    Add an immediate value and a register, store the result into a register

    Syntax:

    `addi x dst, x reg, m`

    where `(dst reg m : UInt64)`.
  -/
  | AddImmediate      : RegisterName → RegisterName → UInt64 → Instr
  /--
    Increment the content of a register by one

    Syntax:

    `inc x dst`

    where `(dst : UInt64)`.
  -/
  | AddNegImmediate      : RegisterName → RegisterName → UInt64 → Instr
  /--
    Decrement the content of a register by one, essentially the same as SubImmediate
    but necessary for correct delaboration.

    Syntax:

    `inc x dst`

    where `(dst : UInt64)`.
  -/
  | Increment         : RegisterName → Instr
  /--
    Add the contents of two registers and store the value into a register

    Syntax:

    `add x dst, x reg1, x reg2`

    where `(dst reg1 reg2 : UInt64)`.
  -/
  | AddRegister       : RegisterName → RegisterName → RegisterName → Instr
  /--
    Subtract an immediate value form a register, store the result into a
    third register

    Syntax:

    `subi x dst, x reg, n`

    where `(dst reg n : UInt64)`.
  -/
  | SubImmediate      : RegisterName → RegisterName → UInt64 → Instr
  /--
    Decrement the content of a register by one

    Syntax:

    `dec x dst`

    where `(dst : UInt64)`.
  -/
  | Decrement         : RegisterName → Instr
  /--
    Subtract the value of a register form another register,
    store the result into a third register

    Syntax:

    `sub x dst, x reg1, x reg2`

    where `(dst reg1 reg2 : UInt64)`.
  -/
  | SubRegister       : RegisterName → RegisterName → RegisterName → Instr
  /--
    Bitwise-XOR operation between an immediate value and the content of a
    register, store the result into a register

    Syntax:

    `xor x dst, x reg, n`

    where `(dst reg n : UInt64)`.
  -/
  | XorImmediate      : RegisterName → RegisterName → UInt64 → Instr
  /--
    Bitwise-XOR operation between the contents of two registers,
    store the result into a third register

    Syntax:

    `xor x dst, x reg1, x reg2`

    where `(dst reg1 reg2 : UInt64)`.
  -/
  | XOR               : RegisterName → RegisterName → RegisterName → Instr
  /--
    Load the content of the memory at the address which provided as an
    immedtiate value into a register

    Syntax:

    `lw x dst, mem_addr`

    where `(dst mem_addr : UInt64)`.
  -/
  | LoadWordImmediate : RegisterName → UInt64 → Instr
  /--
    Load the content of the memory at the address which is stored in a register
    into a register

    Syntax:

    `lw x dst, x reg_with_mem_addr`

    where `(dst reg_with_mem_addr : UInt64)`.
  -/
  | LoadWordReg       : RegisterName → UInt64 → RegisterName → Instr
  /--
    Load the content of a register into the memory at the address which is
    stored in a register

    Syntax:

    `sw x reg_with_value, x reg_with_mem_addr`

    where `(reg_with_value reg_with_mem_addr : UInt64)`.
  -/
  | StoreWord         : RegisterName → UInt64 → RegisterName → Instr
  /--
    Jump to a given labelname.

    Syntax:

    `j label`

    where `(label : ident)`.

    Note: Due to the elaboration, the actual syntax does not require a `String`
    but an identifier (`ident`). Therefore, there is no need to use quotation
    marks to represent a sequence of characters as a string type.
    This is also true for all the following conditional jump instuctions
  -/
  | Jump              : String → Instr
  /--
    Jump to a given labelname when the contents of two provided registers are
    equal

    Syntax:

    `beq x reg1, x reg2, label`

    where `(reg1 reg2 : UInt64) (label : ident)`.
  -/
  | JumpEq            : RegisterName → RegisterName → String → Instr
  /--
    Jump to a given labelname when the contents of two provided registers are
    not equal

    Syntax:

    `bne x reg1, x reg2, label`

    where `(reg1 reg2 : UInt64) (label : ident)`.
  -/
  | JumpNeq           : RegisterName → RegisterName → String → Instr
  /--
    Jump to a given labelname when the content of the first register provided
    is greater than the content of the other register provided.

    Syntax:

    `bgt x reg1, x reg2, label`

    where `(reg1 reg2 : UInt64) (label : ident)`.
  -/
  | JumpGt            : RegisterName → RegisterName → String → Instr
  /--
    Jump to a given labelname when the content of the first register provided
    is less or equal the content of the other register provided.

    Syntax:

    `ble x reg1, x reg2, label`

    where `(reg1 reg2 : UInt64) (label : ident)`.
  -/
  | JumpLe            : RegisterName → RegisterName → String → Instr
  /--
    Jump to a given labelname when the content of the register provided
    is equal to zero.

    Syntax:

    `beqz x reg, label`

    where `(reg : UInt64) (label : ident)`.
  -/
  | JumpEqZero        : RegisterName → String → Instr
  /--
    Jump to a given labelname when the content of the first register provided
    is greater than the content of the other register provided.

    Syntax:

    `bnez x reg, label`

    where `(reg : UInt64) (label : ident)`.
  -/
  | JumpNeqZero       : RegisterName → String → Instr
  /--
    Default instruction, sets the terminated flag to true
  -/
  | Panic             : Instr
  deriving BEq, Inhabited


/--
ToString for delaboration
-/
instance : ToString Instr where
  toString
    | Instr.LoadAddress dst addr =>
      -- For calculate the amount of zeros after `0x`to cut them off the string
      let hex := addr.toBitVec.zeroExtend (Nat.log2 addr.toNat + 1)
      s!"la {dst}, {hex}"
    | Instr.LoadImmediate dst i => s!"li {dst}, {i}"
    | Instr.LoadNegImmediate dst i => s!"li {dst}, -{i}"
    | Instr.CopyRegister dst src => s!"mv {dst} , {src}"
    | Instr.AddImmediate dst reg i => s!"addi {dst}, {reg}, {i}"
    | Instr.AddNegImmediate dst reg i => s!"addi {dst}, {reg}, -{i}"
    | Instr.Increment dst => s!"inc {dst}"
    | Instr.AddRegister dst reg1 reg2 => s!"add {dst}, {reg1}, {reg2}"
    | Instr.SubImmediate dst reg i => s!"subi {dst}, {reg}, {i}"
    | Instr.Decrement dst => s!"dec {dst}"
    | Instr.SubRegister dst reg1 reg2 => s!"sub {dst}, {reg1}, {reg2}"
    | Instr.XorImmediate dst reg i => s!"xori {dst}, {reg}, {i}"
    | Instr.XOR dst reg1 reg2 => s!"xor {dst}, {reg1}, {reg2}"
    | Instr.LoadWordImmediate dst addr =>
      -- For calculate the amount of zeros after `0x`to cut them off the string
      let hex := addr.toBitVec.zeroExtend (Nat.log2 addr.toNat + 1)
      s!"lw {dst}, {hex}"
    | Instr.LoadWordReg dst off addr => s!"lw {dst}, {off}({addr})"
    | Instr.StoreWord reg off dst => s!"sw {reg}, {off}({dst})"
    | Instr.Jump lbl => s!"j {lbl}"
    | Instr.JumpEq reg1 reg2 lbl => s!"beq {reg1}, {reg2}, {lbl}"
    | Instr.JumpNeq reg1 reg2 lbl => s!"bne {reg1}, {reg2}, {lbl}"
    | Instr.JumpGt reg1 reg2 lbl => s!"bgt {reg1}, {reg2}, {lbl}"
    | Instr.JumpLe reg1 reg2 lbl => s!"ble {reg1}, {reg2}, {lbl}"
    | Instr.JumpEqZero reg lbl => s!"beqz {reg}, {lbl}"
    | Instr.JumpNeqZero reg lbl => s!"bnez {reg}, {lbl}"
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

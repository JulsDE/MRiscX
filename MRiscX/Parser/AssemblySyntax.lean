import Lean
open Lean Parser
/-
In this file, we extend Lean by introducing a new term. This term allows
us to write assembly language source code, which can then be elaborated
into a form that is processable, which will be the Code structure.
To do so, the syntax needs to be defined. Furthermore, the syntax
should be elevated to the `Code` structure. For this, the syntax need to be
converted into the abstract syntax tree called `Expr`.
In order to understand this, the syntax and semantics of the MRiscX language should be present.

First of all, we define some syntax categories
-/

declare_syntax_cat mriscx_label
 -- behaviour := both controls the behavior whether lean parser
 -- wants to parse func name as token / ident
declare_syntax_cat mriscx_registers (behavior := both)
declare_syntax_cat mriscx_Instr (behavior := both)
declare_syntax_cat mriscx_syntax
declare_syntax_cat mriscx_program
declare_syntax_cat mriscx_num_or_ident
declare_syntax_cat hoare

-- this cat is for making it easier to differentiate between single line
-- proofs and hole code snippets. Its specially for specifications.
declare_syntax_cat mriscx_spec

/-
Next, we define the syntax that will be valid within our language. Since we aim
to prove statements based on this language, it is essential to support numerical
literals (num) and variables as integers (ident).
-/
syntax num : mriscx_num_or_ident

syntax ident : mriscx_num_or_ident

syntax &"x0" : mriscx_registers
syntax &"zero" : mriscx_registers

syntax &"x1" : mriscx_registers
syntax &"ra" : mriscx_registers

syntax &"x2" : mriscx_registers
syntax &"sp" : mriscx_registers

syntax &"x3" : mriscx_registers
syntax &"gp" : mriscx_registers

syntax &"x4" : mriscx_registers
syntax &"tp" : mriscx_registers

syntax &"x5" : mriscx_registers
syntax &"t0" : mriscx_registers

syntax &"x6" : mriscx_registers
syntax &"t1" : mriscx_registers
syntax &"x7" : mriscx_registers
syntax &"t2" : mriscx_registers

syntax &"x8" : mriscx_registers
syntax &"s0" : mriscx_registers
syntax &"fp" : mriscx_registers

syntax &"x9" : mriscx_registers
syntax &"s1" : mriscx_registers

syntax &"x10" : mriscx_registers
syntax &"a0" : mriscx_registers

syntax &"x11" : mriscx_registers
syntax &"a1" : mriscx_registers

syntax &"x12" : mriscx_registers
syntax &"a2" : mriscx_registers

syntax &"x13" : mriscx_registers
syntax &"a3" : mriscx_registers

syntax &"x14" : mriscx_registers
syntax &"a4" : mriscx_registers

syntax &"x15" : mriscx_registers
syntax &"a5" : mriscx_registers

syntax &"x16" : mriscx_registers
syntax &"a6" : mriscx_registers

syntax &"x17" : mriscx_registers
syntax &"a7" : mriscx_registers

syntax &"x18" : mriscx_registers
syntax &"s2" : mriscx_registers

syntax &"x19" : mriscx_registers
syntax &"s3" : mriscx_registers

syntax &"x20" : mriscx_registers
syntax &"s4" : mriscx_registers

syntax &"x21" : mriscx_registers
syntax &"s5" : mriscx_registers

syntax &"x22" : mriscx_registers
syntax &"s6" : mriscx_registers

syntax &"x23" : mriscx_registers
syntax &"s7" : mriscx_registers

syntax &"x24" : mriscx_registers
syntax &"s8" : mriscx_registers

syntax &"x25" : mriscx_registers
syntax &"s9" : mriscx_registers

syntax &"x26" : mriscx_registers
syntax &"s10" : mriscx_registers

syntax &"x27" : mriscx_registers
syntax &"s11" : mriscx_registers


syntax &"x28" : mriscx_registers
syntax &"t3" : mriscx_registers

syntax &"x29" : mriscx_registers
syntax &"t4" : mriscx_registers

syntax &"x30" : mriscx_registers
syntax &"t5" : mriscx_registers

syntax &"x31" : mriscx_registers
syntax &"t6" : mriscx_registers

syntax &"x" mriscx_num_or_ident : mriscx_registers
/-
Now we can define the syntax of all the legal instructions we need for our program.
-/
/-
Operations in registers
-/
syntax "la " mriscx_registers &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "li " mriscx_registers &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "mv " mriscx_registers &"," mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "addi " mriscx_registers &", " mriscx_registers &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "inc " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "add " mriscx_registers ", " mriscx_registers &", " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "subi " mriscx_registers ", " mriscx_registers &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "dec " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "sub " mriscx_registers ", " mriscx_registers &", " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "xori " mriscx_registers ", " mriscx_registers &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "xor " mriscx_registers ", " mriscx_registers &", " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Operations on memory
-/
-- Load word immediately from address
syntax "lw " mriscx_registers ", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
-- Load word from address stored in register
syntax "lw " mriscx_registers ", " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
-- Store word stored in register
-- The first register is the source, the second holds the destination address
syntax "sw " mriscx_registers ", " mriscx_registers
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Flow control operations
-/
syntax &"j " ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax &"j " &"." ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beq " mriscx_registers &", " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beq " mriscx_registers &", " mriscx_registers &", "  &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bne " mriscx_registers &", " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bne " mriscx_registers &", " mriscx_registers &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bgt " mriscx_registers &", " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bgt " mriscx_registers &", " mriscx_registers &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "ble " mriscx_registers &", " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "ble " mriscx_registers &", " mriscx_registers &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beqz " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beqz " mriscx_registers &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bnez " mriscx_registers &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bnez " mriscx_registers &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Default instruction
-/
syntax "PANIC!" withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
The labels followed by the instructions
-/
syntax ppDedent(ppDedent(ppLine)) ident ": " mriscx_Instr* : mriscx_label
syntax ppDedent(ppDedent(ppLine)) &"." ident ": " mriscx_Instr* : mriscx_label


syntax "mriscx" withPosition(linebreak)
  mriscx_label*
  ppDedent("end") : mriscx_syntax

syntax mriscx_syntax : term


/-
Brackets to indicate specification of instruction
-/
syntax "⟪" mriscx_Instr "⟫": mriscx_spec

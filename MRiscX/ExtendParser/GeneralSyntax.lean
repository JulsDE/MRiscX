import MRiscX.ExtendParser.AbstractSyntaxForGen
import Mathlib.Data.Set.Basic

import Lean

open Lean
open Lean Elab Command
open Lean.Parser.Command
open Lean.Parser.Term








open Lean Elab Command Term
/-
Minimal placeholder categories used by generated instruction syntax.
-/
declare_syntax_cat register (behavior := both)
declare_syntax_cat register_bare (behavior := both)
declare_syntax_cat register_abi (behavior := both)
declare_syntax_cat immediate
declare_syntax_cat label
declare_syntax_cat num_or_ident

syntax num : num_or_ident
syntax ident : num_or_ident

syntax &"x" num_or_ident : register
syntax register_bare : register
syntax register_abi : register

syntax &"x0" : register_bare
syntax &"x1" : register_bare
syntax &"x2" : register_bare
syntax &"x3" : register_bare
syntax &"x4" : register_bare
syntax &"x5" : register_bare
syntax &"x6" : register_bare
syntax &"x7" : register_bare
syntax &"x8" : register_bare
syntax &"x9" : register_bare
syntax &"x10" : register_bare
syntax &"x11" : register_bare
syntax &"x12" : register_bare
syntax &"x13" : register_bare
syntax &"x14" : register_bare
syntax &"x15" : register_bare
syntax &"x16" : register_bare
syntax &"x17" : register_bare
syntax &"x18" : register_bare
syntax &"x19" : register_bare
syntax &"x20" : register_bare
syntax &"x21" : register_bare
syntax &"x22" : register_bare
syntax &"x23" : register_bare
syntax &"x24" : register_bare
syntax &"x25" : register_bare
syntax &"x26" : register_bare
syntax &"x27" : register_bare
syntax &"x28" : register_bare
syntax &"x29" : register_bare
syntax &"x30" : register_bare
syntax &"x31" : register_bare

syntax &"zero" : register_abi
syntax &"ra" : register_abi
syntax &"sp" : register_abi
syntax &"gp" : register_abi
syntax &"tp" : register_abi
syntax &"t0" : register_abi
syntax &"t1" : register_abi
syntax &"t2" : register_abi
syntax &"s0" : register_abi
syntax &"fp" : register_abi
syntax &"s1" : register_abi
syntax &"a0" : register_abi
syntax &"a1" : register_abi
syntax &"a2" : register_abi
syntax &"a3" : register_abi
syntax &"a4" : register_abi
syntax &"a5" : register_abi
syntax &"a6" : register_abi
syntax &"a7" : register_abi
syntax &"s2" : register_abi
syntax &"s3" : register_abi
syntax &"s4" : register_abi
syntax &"s5" : register_abi
syntax &"s6" : register_abi
syntax &"s7" : register_abi
syntax &"s8" : register_abi
syntax &"s9" : register_abi
syntax &"s10" : register_abi
syntax &"s11" : register_abi
syntax &"t3" : register_abi
syntax &"t4" : register_abi
syntax &"t5" : register_abi
syntax &"t6" : register_abi

syntax num_or_ident : immediate
syntax ident : label

/-
Target instruction/program categories.
`mkSyntax` adds concrete instruction forms into `mriscx_Instr`.
-/
declare_syntax_cat mriscx_Instr (behavior := both)
declare_syntax_cat mriscx_label
declare_syntax_cat mriscx_syntax

syntax ppDedent(ppDedent(ppLine)) ident ": " mriscx_Instr* : mriscx_label

syntax "mriscx" withPosition(linebreak)
  mriscx_label+
  ppDedent("end") : mriscx_syntax

syntax (name := mriscxTerm) mriscx_syntax : term






syntax num : num_or_ident
syntax ident : num_or_ident

syntax &"x" num_or_ident : register
syntax "x0" : register

syntax num_or_ident : immediate
syntax ident : label

declare_syntax_cat instr_set_hoare_assignment
declare_syntax_cat instr_set_hoare_assignment_chain
declare_syntax_cat instr_set_hoare_assignment_term

syntax "x[" num_or_ident "]" "←" term : instr_set_hoare_assignment
syntax "x[" num_or_ident "]" "<-" term : instr_set_hoare_assignment
syntax "x[" register "]" "←" term : instr_set_hoare_assignment
syntax "x[" register "]" "<-" term : instr_set_hoare_assignment
syntax "mem[" term &"]" "←" term : instr_set_hoare_assignment
syntax "mem[" term &"]" "<-" term : instr_set_hoare_assignment
syntax ident "++" : instr_set_hoare_assignment
syntax ident "←" term : instr_set_hoare_assignment
syntax ident "<-" term : instr_set_hoare_assignment

syntax "⟦⟧" : instr_set_hoare_assignment_term
syntax instr_set_hoare_assignment : instr_set_hoare_assignment_chain
syntax instr_set_hoare_assignment ";" instr_set_hoare_assignment : instr_set_hoare_assignment_chain
syntax instr_set_hoare_assignment ";" instr_set_hoare_assignment_chain : instr_set_hoare_assignment_chain
syntax "⟦" instr_set_hoare_assignment_chain "⟧" : instr_set_hoare_assignment_term

syntax "⟦⟧" : term
syntax "⟦" instr_set_hoare_assignment_chain "⟧" : term
syntax "x[" register "]" : term
syntax "x[" num_or_ident "]" : term
syntax "mem[" term "]" : term
syntax "labels[" ident "]" : term
syntax "labels[" &"." ident "]" : term
syntax "⸨pc⸩" : term
syntax "⸨terminated⸩": term

declare_syntax_cat instr_set_hole
syntax register : instr_set_hole
syntax immediate : instr_set_hole
syntax label : instr_set_hole
syntax "(" ident ":" stx ")" : instr_set_hole

declare_syntax_cat instr_set_piece
syntax instr_set_hole : instr_set_piece
syntax ident : instr_set_piece
syntax num   : instr_set_piece
syntax str   : instr_set_piece
syntax char  : instr_set_piece
syntax ","   : instr_set_piece
syntax ";"   : instr_set_piece
syntax ":"   : instr_set_piece
syntax "."   : instr_set_piece
syntax "+"   : instr_set_piece
syntax "-"   : instr_set_piece
syntax "*"   : instr_set_piece
syntax "/"   : instr_set_piece
syntax "="   : instr_set_piece
syntax "<"   : instr_set_piece
syntax ">"   : instr_set_piece
syntax "<="  : instr_set_piece
syntax ">="  : instr_set_piece

declare_syntax_cat instr_set_sig
syntax ((!( ("," "semantics" ":") )) instr_set_piece)+ : instr_set_sig

declare_syntax_cat instr_set_spec
-- syntax instr_set_spec : term
syntax "⦃" term "⦄" term "↦" "⟨" term "|" term "⟩" "⦃" term "⦄" : instr_set_spec
syntax ((!("⦃")) term) : instr_set_spec

declare_syntax_cat instr_set_entry
syntax ident ":" "{"
  "syntax" ":" instr_set_sig ","
  "semantics" ":" term ","
  "specification" ":" instr_set_spec
  "}" : instr_set_entry
syntax ident ":" "{"
  "syntax" ":" instr_set_sig ","
  "semantics" ":" term
  ppLine "specification" ":" instr_set_spec
  "}" : instr_set_entry

syntax (name := mkInstrSetTerm)
  "mkInstrSet " ident ident ident ppLine withPosition((colGe instr_set_entry)+) : term

syntax (name := mkTypeCmd)
  "mkType " ident : command

syntax (name := mkExecutionCmd)
  "mkExecution " ident : command

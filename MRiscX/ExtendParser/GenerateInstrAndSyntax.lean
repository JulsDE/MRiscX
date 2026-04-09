import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.ExprDecoder
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
import Mathlib.Data.Set.Basic
import Lean

open Lean
open Lean Elab Command
open Lean.Parser.Command
open Lean.Parser.Term

/-
  Placeholders used in instruction syntax signatures.
-/


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


/-! Persisted internal representation -/

structure Hole where
  name   : Name
  ty     : String
  parser : String
deriving Repr, Inhabited, ToExpr

inductive Piece where
  | lit  (token : String)
  | hole (value : Hole)
deriving Repr, Inhabited, ToExpr

structure CtorSpec where
  ref      : String
  ctorName : Name
  pieces   : Array Piece
  sem      : String
  spec     : String
deriving Repr, Inhabited, ToExpr

structure ArchSpec where
  name     : Name
  typeName : Name
  execName : Name
  specs    : Array CtorSpec
deriving Repr, Inhabited, ToExpr


/-! Helpers -/

private partial def leafTokenText? : Syntax → Option String
  | Syntax.ident _ rawVal _ _ =>
      some (toString rawVal)
  | Syntax.atom _ val =>
      some val
  | Syntax.node _ _ args =>
      let rec go (i : Nat) : Option String :=
        if h : i < args.size then
          match leafTokenText? (args[i]'h) with
          | some s => some s
          | none   => go (i + 1)
        else
          none
      go 0
  | Syntax.missing =>
      none

private def joinLines (xs : List String) : String :=
  String.intercalate "\n" xs

private def parseCommandStr (ref : Syntax) (s : String) : CommandElabM (TSyntax `command) := do
  match Parser.runParserCategory (← getEnv) `command s "<mkInstrSet>" with
  | .ok stx =>
      pure ⟨stx⟩
  | .error err =>
      throwErrorAt ref s!"generated command failed:\n\n{s}\n\n{err}"


/-! Parse DSL into persisted specs -/

private def fieldsOfInputPieces (pieces : Array Piece) : Array Hole :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _    => acc
    | .hole h   => acc.push h

private def ensureNoDuplicateFieldNames
    (ctorName : Name)
    (fields : Array Hole) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for h in fields do
    let n := h.name.eraseMacroScopes
    if seen.contains n then
      throwError s!"duplicate placeholder name `{n}` in constructor `{ctorName}`"
    seen := seen.push n

private def elabPiece (piece : TSyntax `instr_set_piece) : CommandElabM Piece := do
  match piece with
  | `(instr_set_piece| $h:instr_set_hole) =>
      match h with
      | `(instr_set_hole| ($name:ident : $parser:stx)) =>
          let n := name.getId.eraseMacroScopes
          match parser with
          | `(stx | register) =>
              pure <| .hole { name := n, ty := "RegisterName", parser := "register" }
          | `(stx | label) =>
              pure <| .hole { name := n, ty := "String", parser := "label" }
          | `(stx | immediate) =>
              pure <| .hole { name := n, ty := "UInt64", parser := "immediate" }
          | _ =>
              throwErrorAt parser "unknown hole parser category (expected register | immediate | label)"
      | _ =>
          throwErrorAt h "invalid placeholder"
  | _ =>
      match leafTokenText? piece.raw with
      | some tok =>
          pure <| .lit tok
      | none =>
          throwErrorAt piece "failed to reconstruct token text"

private def extractPieces
    (sig : TSyntax `instr_set_sig) :
    CommandElabM (Array Piece) := do
  match sig with
  | `(instr_set_sig| $[$pieces:instr_set_piece]*) =>
      pieces.mapM elabPiece
  | _ =>
      throwErrorAt sig "invalid syntax signature"

private def mkCtorSpec
    (entry : TSyntax `instr_set_entry) :
    CommandElabM CtorSpec := do
  match entry with
  | `(instr_set_entry| $ctorName:ident : { syntax : $sig:instr_set_sig, semantics : $sem:term, specification : $spec:instr_set_spec }) => do
      let pieces ← extractPieces sig
      let holes := fieldsOfInputPieces pieces
      let ctorName := ctorName.getId.eraseMacroScopes
      ensureNoDuplicateFieldNames ctorName holes
      pure {
        ref      := entry.raw.reprint.getD (toString entry.raw)
        ctorName := ctorName
        pieces   := pieces
        sem      := sem.raw.reprint.getD (toString sem.raw)
        spec     := spec.raw.reprint.getD (toString spec.raw)
      }
  | `(instr_set_entry| $ctorName:ident : { syntax : $sig:instr_set_sig, semantics : $sem:term
      specification : $spec:instr_set_spec }) => do
      let pieces ← extractPieces sig
      let holes := fieldsOfInputPieces pieces
      let ctorName := ctorName.getId.eraseMacroScopes
      ensureNoDuplicateFieldNames ctorName holes
      pure {
        ref      := entry.raw.reprint.getD (toString entry.raw)
        ctorName := ctorName
        pieces   := pieces
        sem      := sem.raw.reprint.getD (toString sem.raw)
        spec     := spec.raw.reprint.getD (toString spec.raw)
      }
  | _ =>
      throwErrorAt entry "invalid instruction entry"


/-! Code generation from persisted ArchSpec -/

private def fieldsOfDecodedPieces (pieces : Array DecodedPiece) : Array DecodedHole :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push h

private def mkCtorTypeText (typeName : Name) (holes : Array DecodedHole) : String :=
  let resultTy := toString typeName
  if holes.isEmpty then
    resultTy
  else
    let argTys := holes.toList.map (fun h => h.tyText)
    String.intercalate " → " (argTys ++ [resultTy])

private def mkCtorLine (typeName : Name) (spec : DecodedCtor) : String :=
  let ctor := toString spec.ctorName
  let ty := mkCtorTypeText typeName (fieldsOfDecodedPieces spec.pieces)
  s!"  | {ctor} : {ty}"

private def mkInductiveCmd
    (arch : DecodedArch) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let ctorLines := arch.ctors.toList.map (mkCtorLine typeName)
  let cmdText := joinLines <|
    [s!"inductive {typeName} : Type where"] ++
    ctorLines ++
    ["deriving Repr, BEq, Inhabited"]
  parseCommandStr Syntax.missing cmdText

private def mkPatArgText (h : DecodedHole) : String :=
  s!"({h.name} : {h.tyText})"

private def mkAltLine (spec : DecodedCtor) : String :=
  let ctor := toString spec.ctorName
  let holes := fieldsOfDecodedPieces spec.pieces
  let pat :=
    if holes.isEmpty then
      s!".{ctor}"
    else
      let args := String.intercalate " " (holes.toList.map mkPatArgText)
      s!".{ctor} {args}"
  s!"  | {pat} => ({spec.semText}) _ms"

private def mkExecuteCmd
    (arch : DecodedArch) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let execName := arch.execName
  let altLines := arch.ctors.toList.map mkAltLine
  let cmdText := joinLines <|
    [ s!"def {execName} (_ms : MState {typeName}) (_instr : {typeName}) : MState {typeName} :="
    , "  match _instr with"
    ] ++
    altLines
  parseCommandStr Syntax.missing cmdText

/-! Elaborators -/

def elabMkInstrSetTerm : Lean.Elab.Term.TermElab := fun stx _expectedType? => do
  match stx with
  | `(term| mkInstrSet $archName:ident $typeName:ident $execName:ident $entries:instr_set_entry*) => do
      let specs ← liftM <| liftCommandElabM (entries.mapM mkCtorSpec)
      let arch : ArchSpec := {
        name     := archName.getId.eraseMacroScopes
        typeName := typeName.getId.eraseMacroScopes
        execName := execName.getId.eraseMacroScopes
        specs    := specs
      }

      pure (toExpr arch)
  | _ =>
      throwUnsupportedSyntax

def elabMkType : CommandElab := fun stx => do
  match stx with
  | `(command| mkType $archName:ident) => do
      let arch ← resolveArchFromIdent archName
      let indCmd ← mkInductiveCmd arch
      elabCommand indCmd
  | _ =>
      throwUnsupportedSyntax

def elabMkExecution : CommandElab := fun stx => do
  match stx with
  | `(command| mkExecution $archName:ident) => do
      let arch ← resolveArchFromIdent archName
      let execCmd ← mkExecuteCmd arch
      elabCommand execCmd
  | _ =>
      throwUnsupportedSyntax

@[term_elab mkInstrSetTerm]
def elabMkInstrSetTermImpl : Lean.Elab.Term.TermElab :=
  elabMkInstrSetTerm

@[command_elab mkTypeCmd]
def elabMkTypeImpl : CommandElab :=
  elabMkType

@[command_elab mkExecutionCmd]
def elabMkExecutionImpl : CommandElab :=
  elabMkExecution

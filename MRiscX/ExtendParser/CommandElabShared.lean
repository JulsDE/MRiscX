import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.GeneralSyntax
import Lean

open Lean
open Lean Elab Command

namespace MRiscX.ExtendParser.CommandElabShared

def joinLines (xs : List String) : String :=
  String.intercalate "\n" xs

def trimAsciiStr (s : String) : String :=
  (s.trimAscii).toString

partial def leafTokenText? : Syntax → Option String
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

def parserTextEq (p : String) (expected : String) : Bool :=
  p == expected || p.endsWith s!".{expected}"

def parseCommandStr
    (ref : Syntax)
    (s : String)
    (origin : String := "<generated>") :
    CommandElabM (TSyntax `command) := do
  let rec reanchor (stx : Syntax) : Syntax :=
    match stx with
    | .node _ k args =>
        .node (.fromRef ref (canonical := true)) k (args.map reanchor)
    | .atom _ val =>
        .atom (.fromRef ref (canonical := true)) val
    | .ident _ rawVal val preresolved =>
        .ident (.fromRef ref (canonical := true)) rawVal val preresolved
    | .missing =>
        .missing
  match Parser.runParserCategory (← getEnv) `command s origin with
  | .ok stx =>
      pure ⟨reanchor stx⟩
  | .error err =>
      throwErrorAt ref s!"generated command failed:\n\n{s}\n\n{err}"

def fieldsOfInputPieces (pieces : Array Piece) : Array Hole :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _    => acc
    | .hole h   => acc.push h

def ensureNoDuplicateFieldNames
    (ctorName : Name)
    (fields : Array Hole) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for h in fields do
    let n := h.name.eraseMacroScopes
    if seen.contains n then
      throwError s!"duplicate placeholder name `{n}` in constructor `{ctorName}`"
    seen := seen.push n

def elabPiece (piece : TSyntax `instr_set_piece) : CommandElabM Piece := do
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

def extractPieces
    (sig : TSyntax `instr_set_sig) :
    CommandElabM (Array Piece) := do
  match sig with
  | `(instr_set_sig| $[$pieces:instr_set_piece]*) =>
      pieces.mapM elabPiece
  | _ =>
      throwErrorAt sig "invalid syntax signature"

def mkInstrSpecFromEntry
    (entry : TSyntax `instr_set_entry) :
    CommandElabM InstrSpec := do
  match entry with
  | `(instr_set_entry| $ctorName:ident : { syntax : $sig:instr_set_sig, semantics : $sem:term, specification : $spec:instr_set_spec }) => do
      let pieces ← extractPieces sig
      let holes := fieldsOfInputPieces pieces
      let ctorName := ctorName.getId.eraseMacroScopes
      let instrSpec : InstrSpec := {
          instrName := ctorName,
          ref := entry.raw.reprint.getD (toString entry.raw),
          pieces := pieces,
          sem := sem.raw.reprint.getD (toString sem.raw),
          hoareDesc := spec
      }
      ensureNoDuplicateFieldNames ctorName holes
      return instrSpec
  | _ =>
      throwErrorAt entry "invalid instruction entry"

end MRiscX.ExtendParser.CommandElabShared

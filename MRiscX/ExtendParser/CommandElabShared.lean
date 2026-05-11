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

private def mkHolePiece (name : TSyntax `ident) (parser : TSyntax `stx) : CommandElabM Piece := do
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

private def sliceStr (s : String.Slice) : String :=
  s.toString

private def removeWhitespace (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    if c.isWhitespace then acc else acc ++ String.singleton c

private def tryElabWrappedHole? (h : TSyntax `instr_set_hole) : CommandElabM (Option (Array Piece)) := do
  let txt := trimAsciiStr (h.raw.reprint.getD (toString h.raw))
  let compact := removeWhitespace txt
  if !(compact.startsWith "((" && compact.endsWith "))") then
    return none
  if compact.length < 4 then
    return none
  let inner := trimAsciiStr (sliceStr ((compact.drop 2).dropEnd 2))
  let holeTxt := "(" ++ inner ++ ")"
  match Parser.runParserCategory (← getEnv) `instr_set_hole holeTxt "<mkAll>" with
  | .ok holeStx =>
      let hInner : TSyntax `instr_set_hole := ⟨holeStx⟩
      match hInner with
      | `(instr_set_hole| ($name:ident : $parser:stx)) =>
          return some #[.lit "(", (← mkHolePiece name parser), .lit ")"]
      | _ =>
          throwErrorAt h "invalid wrapped placeholder `((name:parser))`"
  | .error _ =>
      return none

private def elabPieceCore (piece : TSyntax `instr_set_piece) : CommandElabM (Array Piece) := do
  match piece with
  | `(instr_set_piece| $h:instr_set_hole) =>
      if let some expanded ← tryElabWrappedHole? h then
        return expanded
      match h with
      | `(instr_set_hole| ($name:ident : $parser:stx)) =>
          pure #[← mkHolePiece name parser]
      | _ =>
          throwErrorAt h "invalid placeholder"
  | _ =>
      match leafTokenText? piece.raw with
      | some tok =>
          pure #[.lit tok]
      | none =>
          throwErrorAt piece "failed to reconstruct token text"

private partial def elabPieceNode (stx : Syntax) : CommandElabM (Array Piece) := do
  if stx.getKind == `group && stx.getArgs.size == 1 then
    elabPieceNode (stx.getArg 0)
  else if stx.getKind == `choice then
    try
      elabPieceNode (stx.getArg 0)
    catch _ =>
      elabPieceNode (stx.getArg 1)
  else
    elabPieceCore (⟨stx⟩ : TSyntax `instr_set_piece)

def extractPieces
    (sig : TSyntax `instr_set_sig) :
    CommandElabM (Array Piece) := do
  let args := sig.raw.getArgs
  let pieceNodes :=
    if args.size == 1 && (args[0]!).getKind == `null then
      (args[0]!).getArgs
    else
      args
  let mut out : Array Piece := #[]
  for node in pieceNodes do
    out := out ++ (← elabPieceNode node)
  pure out

def mkInstrSpecFromEntry
    (entry : TSyntax `instr_set_entry) :
    CommandElabM InstrSpec := do
  match entry with
  | `(instr_set_entry| $ctorName:ident : {
                          syntax : $sig:instr_set_sig,
                          semantics : $sem:term,
                          specification : $spec:instr_set_spec
    }) => do
      let pieces ← extractPieces sig
      let holes := fieldsOfInputPieces pieces
      let ctorName := ctorName.getId.eraseMacroScopes
      let instrSpec : InstrSpec := {
          src := entry.raw
          instrName := ctorName,
          ref := entry.raw.reprint.getD (toString entry.raw),
          pieces := pieces,
          sem := sem,
          hoareDesc := spec
      }
      ensureNoDuplicateFieldNames ctorName holes
      return instrSpec
  | _ =>
      throwErrorAt entry "invalid instruction entry"

end MRiscX.ExtendParser.CommandElabShared

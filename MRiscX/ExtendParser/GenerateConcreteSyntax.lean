import MRiscX.ExtendParser.GeneralSyntax
import MRiscX.ExtendParser.AbstractSyntaxForGen

open Lean Elab Term Command


@[term_elab mriscxTerm]
def elabMriscxSyntax : TermElab := fun stx expectedType? => do
  let _ := stx
  let _ := expectedType?
  throwUnsupportedSyntax

syntax (name := mkSyntaxCmd)
  "mkSyntax " ident : command

/-! Concrete-syntax generation -/

private def quoteStringLit (s : String) : String :=
  let escaped :=
    s.toList.foldl (init := "") fun acc c =>
      acc ++
        match c with
        | '"' => "\\\""
        | '\\' => "\\\\"
        | '\n' => "\\n"
        | '\t' => "\\t"
        | '\r' => "\\r"
        | c    => String.singleton c
  "\"" ++ escaped ++ "\""

private def parseStx (input : String) : CommandElabM (TSyntax `stx) := do
  match Parser.runParserCategory (← getEnv) `stx input "<mkSyntax>" with
  | .ok stx   => pure ⟨stx⟩
  | .error err =>
      throwError s!"error while generating stx from `{input}`:\n{err}"

private def isIdentLikeTok (tok : String) : Bool :=
  let rec loop : List Char → Bool
    | []      => true
    | c :: cs => (c.isAlphanum || c == '_' || c == '\'') && loop cs
  tok.length > 0 && loop tok.toList

private def isPunctuationTok (tok : String) : Bool :=
  tok == ","  || tok == ";"  || tok == ":"  || tok == "." ||
  tok == "+"  || tok == "-"  || tok == "*"  || tok == "/" ||
  tok == "="  || tok == "<"  || tok == ">"  ||
  tok == "<=" || tok == ">="

private def decorateAtomText (tok : String) (isFirst : Bool) (hasNext : Bool) : String :=
  if (tok == "," || tok == ";" || tok == ":") && hasNext then
    tok ++ " "
  else if isIdentLikeTok tok && isFirst && hasNext then
    tok ++ " "
  else
    tok

private def useNonReservedAtom (tok : String) (isFirst : Bool) : Bool :=
  if isIdentLikeTok tok then
    !(isFirst && tok.length > 1)
  else
    isPunctuationTok tok

private def mkLiteralStx (tok : String) (isFirst : Bool) (hasNext : Bool) : CommandElabM (TSyntax `stx) := do
  let txt := decorateAtomText tok isFirst hasNext
  let txtQ := quoteStringLit txt
  if useNonReservedAtom tok isFirst then
    parseStx s!"&{txtQ}"
  else
    parseStx txtQ

private def mkSyntaxItems (spec : InstrSpec) : CommandElabM (Array (TSyntax `stx)) := do
  let mut items : Array (TSyntax `stx) := #[]
  let nPieces := spec.pieces.size
  for i in [0:nPieces] do
    let hasNext := i + 1 < nPieces
    match spec.pieces[i]! with
    | Piece.lit tok =>
        items := items.push (← mkLiteralStx tok (i == 0) hasNext)
    | Piece.hole hole =>
        items := items.push (← parseStx (toString hole.parser))
  let terminator : TSyntax `stx ← `(stx| withPosition(Lean.Parser.semicolonOrLinebreak ppDedent(ppLine)))
  pure <| items.push terminator

def mkSyntaxCmdForCtor (spec : InstrSpec) : CommandElabM (TSyntax `command) := do
  let items ← mkSyntaxItems spec
  `(command| syntax $[$items:stx]* : mriscx_Instr)


-- def elabMkSyntax : CommandElab := fun stx => do
--   match stx with
--   | `(command| mkSyntax $archName:ident) => do
--       let arch ← resolveArchFromIdent archName
--       for ctor in arch.ctors do
--         let cmd ← mkSyntaxCmdForCtor ctor
--         elabCommand cmd
--   | _ =>
--       throwUnsupportedSyntax

-- @[command_elab mkSyntaxCmd]
-- def elabMkSyntaxImpl : CommandElab :=
--   elabMkSyntax

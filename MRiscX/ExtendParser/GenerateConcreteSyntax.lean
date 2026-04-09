import MRiscX.ExtendParser.ExprDecoder

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

private def mkSyntaxItems (spec : DecodedCtor) : CommandElabM (Array (TSyntax `stx)) := do
  let mut items : Array (TSyntax `stx) := #[]
  let nPieces := spec.pieces.size
  for i in [0:nPieces] do
    let hasNext := i + 1 < nPieces
    match spec.pieces[i]! with
    | DecodedPiece.lit tok =>
        items := items.push (← mkLiteralStx tok (i == 0) hasNext)
    | DecodedPiece.hole hole =>
        items := items.push (← parseStx (toString hole.parser))
  let terminator : TSyntax `stx ← `(stx| withPosition(Lean.Parser.semicolonOrLinebreak ppDedent(ppLine)))
  pure <| items.push terminator

private def mkSyntaxCmdForCtor (spec : DecodedCtor) : CommandElabM (TSyntax `command) := do
  let items ← mkSyntaxItems spec
  `(command| syntax $[$items:stx]* : mriscx_Instr)


def elabMkSyntax : CommandElab := fun stx => do
  match stx with
  | `(command| mkSyntax $archName:ident) => do
      let arch ← resolveArchFromIdent archName
      for ctor in arch.ctors do
        let cmd ← mkSyntaxCmdForCtor ctor
        elabCommand cmd
  | _ =>
      throwUnsupportedSyntax

@[command_elab mkSyntaxCmd]
def elabMkSyntaxImpl : CommandElab :=
  elabMkSyntax

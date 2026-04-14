import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.Elab.HandleRegister

open Lean Meta Elab Command

private def joinLines (xs : List String) : String :=
  String.intercalate "\n" xs

private def parseCommandStr (ref : Syntax) (s : String) : CommandElabM (TSyntax `command) := do
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
  match Lean.Parser.runParserCategory (← getEnv) `command s "<mkGetInstrExpr>" with
  | .ok stx =>
      pure ⟨reanchor stx⟩
  | .error err =>
      throwErrorAt ref s!"generated command failed:\n\n{s}\n\n{err}"

private def parserNameEq (p : String) (expected : String) : Bool :=
  p == expected || p.endsWith s!".{expected}"

private def holeNameText (h : Hole) : String :=
  toString (h.name.eraseMacroScopes)

private def holeExprNameText (h : Hole) : String :=
  s!"exprOf_{holeNameText h}"

private def piecePatternText (piece : Piece) : String :=
  match piece with
  | .lit tok =>
      tok
  | .hole h =>
      s!"${holeNameText h}:{h.parser}"

private def mkInstrPatternText (pieces : Array Piece) (withSemicolon : Bool) : String :=
  let body := String.intercalate " " (pieces.toList.map piecePatternText)
  if withSemicolon then
    body ++ " ;"
  else
    body

private def appendName : Name → Name → Name
  | p, .anonymous => p
  | p, .str q s   => .str (appendName p q) s
  | p, .num q n   => .num (appendName p q) n

private def qualifyCtorName (typeName ctorName : Name) : Name :=
  let t := typeName.eraseMacroScopes
  let c := ctorName.eraseMacroScopes
  match c with
  | .str .anonymous _ =>
      appendName t c
  | .num .anonymous _ =>
      appendName t c
  | _ =>
      c

private def mkHoleParseLines
    (spec : InstrSpec) :
    CommandElabM (Array String × Array String) := do
  let mut lines : Array String := #[]
  let mut argExprNames : Array String := #[]
  let mut prevLitTok : Option String := none
  for piece in spec.pieces do
    match piece with
    | .lit tok =>
        prevLitTok := some tok
    | .hole h =>
        let holeName := holeNameText h
        let exprName := holeExprNameText h
        if parserNameEq h.parser "register" then
          lines := lines.push s!"      let {exprName} ← getCorrespondingRegister {holeName}"
        else if parserNameEq h.parser "immediate" then
          lines := lines.push s!"      let {exprName} ←"
          lines := lines.push s!"        match {holeName} with"
          lines := lines.push s!"        | `(immediate | $n:num_or_ident) => parseMriscxNumOrIdent n"
          lines := lines.push s!"        | _ => throwError \"unexpected immediate syntax\""
        else if parserNameEq h.parser "label" then
          let withDotTxt := if prevLitTok == some "." then "true" else "false"
          lines := lines.push s!"      let {exprName} ←"
          lines := lines.push s!"        match {holeName} with"
          lines := lines.push s!"        | `(label | $lbl:ident) => parseLabelname lbl {withDotTxt}"
          lines := lines.push s!"        | _ => throwError \"unexpected label syntax\""
        else
          throwError s!"unsupported placeholder parser `{h.parser}` in instruction `{spec.instrName.eraseMacroScopes}`"
        argExprNames := argExprNames.push exprName
        prevLitTok := none
  pure (lines, argExprNames)

private def mkInstrAltLines (arch : ArchSpec) (spec : InstrSpec) : CommandElabM (List String) := do
  let patNoSemi := mkInstrPatternText spec.pieces false
  let patWithSemi := mkInstrPatternText spec.pieces true
  let (holeParseLines, argExprNames) ← mkHoleParseLines spec
  let ctorConst := toString (qualifyCtorName arch.typeName spec.instrName)
  let ctorArgs :=
    if argExprNames.isEmpty then
      "#[]"
    else
      s!"#[{String.intercalate ", " argExprNames.toList}]"
  let mut lines : Array String := #[
    s!"    | `(mriscx_Instr | {patNoSemi}
    )",
    s!"    | `(mriscx_Instr | {patWithSemi}) => do"
  ]
  for l in holeParseLines do
    lines := lines.push l
  lines := lines.push s!"      return (Lean.mkAppN (Lean.mkConst `{ctorConst}) {ctorArgs})"
  pure lines.toList

def mkGetInstrExprCmd (ref : Syntax) (arch : ArchSpec) : CommandElabM (TSyntax `command) := do
  let mut altLines : List String := []
  for spec in arch.specs do
    altLines := altLines ++ (← mkInstrAltLines arch spec)
  let cmdText := joinLines <|
    ["def getInstrExpr (t : Lean.TSyntax `mriscx_Instr) : Lean.Elab.Term.TermElabM Lean.Expr := do",
     "  match t with"] ++
    altLines ++
    [s!"    | _ => throwError \"unknown instruction for architecture {arch.name.eraseMacroScopes}\""]
  parseCommandStr ref cmdText

def mkTest (ref : Syntax) : CommandElabM (TSyntax `command) := do
  let cmdText := joinLines
    [ "elab \"⟪\" entry:mriscx_Instr \"⟫\" : term => do"
    , "  return (← getInstrExpr entry)"
    ]
  parseCommandStr ref cmdText

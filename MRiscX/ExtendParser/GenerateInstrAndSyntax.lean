import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GeneralSyntax
import MRiscX.ExtendParser.GenerateElaborator
import MRiscX.ExtendParser.GenerateExecuteFunction
import MRiscX.ExtendParser.GenerateInstrSetHoareRewrite
import MRiscX.Elab.HandleRegister
import Mathlib.Data.Set.Basic
import Lean

open Lean
open Lean Elab Command
open Lean.Parser.Command
open MRiscX.ExtendParser.CommandElabShared

private def trimAsciiLocal (s : String) : String :=
  trimAsciiStr s

private def isRegisterHole (h : Hole) : Bool :=
  parserTextEq h.parser "register"

private def isImmediateHole (h : Hole) : Bool :=
  parserTextEq h.parser "immediate"

private def isLabelHole (h : Hole) : Bool :=
  parserTextEq h.parser "label"

private def holesOfSpec (spec : InstrSpec) : Array Hole :=
  spec.pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push h

private def binderTypeText (h : Hole) (hoareStyle : Bool) : String :=
  if hoareStyle then
    if isRegisterHole h then
      "UInt64"
    else if isImmediateHole h then
      "UInt64"
    else if isLabelHole h then
      "String"
    else
      h.ty
  else
    h.ty

private def mkSpecBinderTexts (arch : ArchSpec) (spec : InstrSpec) (hoareStyle : Bool) : Array String := Id.run do
  let mut seen : Array Name := #[]
  let mut binders : Array String := #[]
  if hoareStyle then
    binders := binders.push s!"[runable_mstate : runable (MState {arch.typeName})]"
    binders := binders.push s!"(P : MState {arch.typeName} → Prop)"
    binders := binders.push "(pc : ProgramCounter)"
    seen := seen.push `P
    seen := seen.push `pc
  for h in holesOfSpec spec do
    let n := h.name.eraseMacroScopes
    if !seen.contains n then
      binders := binders.push s!"({n} : {binderTypeText h hoareStyle})"
      seen := seen.push n
  return binders

private def isPunctuationTok (tok : String) : Bool :=
  tok == "," || tok == ";" || tok == ":" || tok == "." ||
  tok == ")" || tok == "]" || tok == "}"

private def isOpenBracketTok (tok : String) : Bool :=
  tok == "(" || tok == "[" || tok == "{"

private def mkInstrCtorArgText (h : Hole) : String :=
  let nameTxt := toString (h.name.eraseMacroScopes)
  if isRegisterHole h then
    s!"(RegisterName.mk (RegisterNr.ofUInt64 {nameTxt}) (@toString UInt64 instToStringUInt64 {nameTxt}))"
  else
    nameTxt

private def instrCtorTextOfSpec (arch : ArchSpec) (spec : InstrSpec) : String :=
  let ctor := s!"{arch.typeName}.{spec.instrName.eraseMacroScopes}"
  let args := (holesOfSpec spec).toList.map mkInstrCtorArgText
  if args.isEmpty then
    ctor
  else
    s!"{ctor} {String.intercalate " " args}"

private def instrTextOfSpec (spec : InstrSpec) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < spec.pieces.size then
      let piece := spec.pieces[i]
      let next? :=
        if hNext : i + 1 < spec.pieces.size then
          some spec.pieces[i + 1]
        else
          none
      let addSpaceAfterHole :=
        match next? with
        | some (.lit tok) => !(isPunctuationTok tok)
        | some _ => true
        | none => false
      let acc :=
        match piece with
        | .lit tok =>
            if tok == "," then
              acc ++ ", "
            else if i == 0 then
              if next?.isSome then acc ++ tok ++ " " else acc ++ tok
            else if isPunctuationTok tok then
              acc ++ tok
            else if isOpenBracketTok tok then
              acc ++ tok
            else
              if next?.isSome then acc ++ tok ++ " " else acc ++ tok
        | .hole h' =>
            let nameTxt := toString (h'.name.eraseMacroScopes)
            let holeTxt := if isRegisterHole h' then s!"x {nameTxt}" else nameTxt
            if addSpaceAfterHole then acc ++ holeTxt ++ " " else acc ++ holeTxt
      go (i + 1) acc
    else
      acc
  trimAsciiLocal (go 0 "")

private def mkSpecDefCmd
    (ref : Syntax)
    (arch : ArchSpec)
    (spec : InstrSpec) :
    CommandElabM (TSyntax `command) := do
  let specName := s!"specification_{spec.instrName.eraseMacroScopes}"
  let rawSpec := trimAsciiLocal (spec.hoareDesc.raw.reprint.getD (toString spec.hoareDesc.raw))
  match spec.hoareDesc with
  | `(instr_set_spec| ⦃$pre:term⦄ $l:term ↦ ⟨$L_w:term | $L_b:term⟩ ⦃$post:term⦄) => do
      let preTxt := pre.raw.reprint.getD (toString pre.raw)
      let postTxt := post.raw.reprint.getD (toString post.raw)
      let lTxt := l.raw.reprint.getD (toString l.raw)
      let LwTxt := L_w.raw.reprint.getD (toString L_w.raw)
      let LbTxt := L_b.raw.reprint.getD (toString L_b.raw)
      let instrCtorTxt := instrCtorTextOfSpec arch spec
      let binders := String.intercalate " " (mkSpecBinderTexts arch spec true).toList
      let cmdTxt := joinLines
        [s!"def {specName} {binders} : Prop :="
        ,s!"  hoare_triple_up_1 (MState {arch.typeName}) {arch.typeName} (Code {arch.typeName}) RegisterName UInt64 ProgramCounter"
        ,s!"    (⧼{preTxt}⧽)"
        ,s!"    (⧼{postTxt}⧽)"
        ,s!"    ({lTxt})"
        ,s!"    ({LwTxt})"
        ,s!"    ({LbTxt})"
        ,s!"    ({instrCtorTxt})"
        ]
      parseCommandStr ref cmdTxt "<mkAll>"
  | _ =>
      let binders := String.intercalate " " (mkSpecBinderTexts arch spec false).toList
      let cmdTxt := joinLines
        [s!"def {specName} {binders} : Prop :="
        ,s!"  {rawSpec}"
        ]
      parseCommandStr ref cmdTxt "<mkAll>"

private def mkCtorTypeText (typeName : Name) (holes : Array Hole) : String :=
  let resultTy := toString typeName
  if holes.isEmpty then
    resultTy
  else
    let argTys := holes.toList.map (fun h => h.ty)
    String.intercalate " → " (argTys ++ [resultTy])

private def mkCtorLine (typeName : Name) (spec : InstrSpec) : String :=
  let ctor := toString spec.instrName
  let ty := mkCtorTypeText typeName (fieldsOfInputPieces spec.pieces)
  s!"  | {ctor} : {ty}"

private def mkInductiveCmd
    (ref : Syntax)
    (arch : ArchSpec) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let ctorLines := arch.specs.toList.map (mkCtorLine typeName)
  let cmdText := joinLines <|
    [s!"inductive {typeName} : Type where"] ++
    ctorLines ++
    ["deriving Repr, BEq, Inhabited"]
  parseCommandStr ref cmdText "<mkAll>"


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

private def parseStx (ref : Syntax) (input : String) : CommandElabM (TSyntax `stx) := do
  match Parser.runParserCategory (← getEnv) `stx input "<mkAllSyntax>" with
  | .ok stx =>
      pure ⟨stx⟩
  | .error err =>
      throwErrorAt ref s!"error while generating stx from `{input}`:\n{err}"

private def isIdentLikeTok (tok : String) : Bool :=
  let rec loop : List Char → Bool
    | []      => true
    | c :: cs => (c.isAlphanum || c == '_' || c == '\'') && loop cs
  tok.length > 0 && loop tok.toList

private def isPunctuationSyntaxTok (tok : String) : Bool :=
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
    isPunctuationSyntaxTok tok

private def mkLiteralStx
    (ref : Syntax)
    (tok : String)
    (isFirst : Bool)
    (hasNext : Bool) :
    CommandElabM (TSyntax `stx) := do
  let txt := decorateAtomText tok isFirst hasNext
  let txtQ := quoteStringLit txt
  if useNonReservedAtom tok isFirst then
    parseStx ref s!"&{txtQ}"
  else
    parseStx ref txtQ

private def mkSyntaxItems (ref : Syntax) (spec : InstrSpec) : CommandElabM (Array (TSyntax `stx)) := do
  let mut items : Array (TSyntax `stx) := #[]
  let nPieces := spec.pieces.size
  for i in [0:nPieces] do
    let hasNext := i + 1 < nPieces
    match spec.pieces[i]! with
    | Piece.lit tok =>
        items := items.push (← mkLiteralStx ref tok (i == 0) hasNext)
    | Piece.hole hole =>
        items := items.push (← parseStx ref (toString hole.parser))
  let terminator : TSyntax `stx ← `(stx| withPosition(Lean.Parser.semicolonOrLinebreak ppDedent(ppLine)))
  pure <| items.push terminator

private def mkInstrSyntaxCmdForCtor (ref : Syntax) (spec : InstrSpec) : CommandElabM (TSyntax `command) := do
  let items ← mkSyntaxItems ref spec
  `(command| syntax $[$items:stx]* : mriscx_Instr)

private def parserNameEq (p : String) (expected : String) : Bool :=
  parserTextEq p expected

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
    s!"    | `(mriscx_Instr | {patNoSemi}\n    )",
    s!"    | `(mriscx_Instr | {patWithSemi}) => do"
  ]
  for l in holeParseLines do
    lines := lines.push l
  lines := lines.push s!"      return (Lean.mkAppN (Lean.mkConst `{ctorConst}) {ctorArgs})"
  pure lines.toList

private def mkGetInstrExprCmd (ref : Syntax) (arch : ArchSpec) : CommandElabM (TSyntax `command) := do
  let mut altLines : List String := []
  for spec in arch.specs do
    altLines := altLines ++ (← mkInstrAltLines arch spec)
  let cmdText := joinLines <|
    ["def getInstrExpr (t : Lean.TSyntax `mriscx_Instr) : Lean.Elab.Term.TermElabM Lean.Expr := do",
     "  match t with"] ++
    altLines ++
    [s!"    | _ => throwError \"unknown instruction for architecture {arch.name.eraseMacroScopes}\""]
  parseCommandStr ref cmdText "<mkAll>"

private def mkTest (ref : Syntax) : CommandElabM (TSyntax `command) := do
  let cmdText := joinLines
    [ "elab \"⟪\" entry:mriscx_Instr \"⟫\" : term => do"
    , "  return (← getInstrExpr entry)"
    ]
  parseCommandStr ref cmdText "<mkAll>"

elab "mkAll " archName:ident typeName:ident execName:ident entries:instr_set_entry*: command => do
  let specs ← entries.mapM mkInstrSpecFromEntry
  let arch : ArchSpec := {
    name     := archName.getId.eraseMacroScopes
    typeName := typeName.getId.eraseMacroScopes
    execName := execName.getId.eraseMacroScopes
    specs    := specs
  }

  let ref := archName.raw
  -- concrete Syntax
  for instr in arch.specs do
    let syn ← mkInstrSyntaxCmdForCtor ref instr
    withRef archName do
      elabCommand syn

  -- inductive type
  let indCmd ← mkInductiveCmd ref arch
  withRef archName do
    elabCommand indCmd
  -- instr to Expr
  withRef archName do
    elabCommand (← mkGetInstrExprCmd ref arch)
  -- Elab for single Instr
  withRef archName do
    elabCommand (← mkTest ref)
  -- Instr Spec
  for instr in arch.specs do
    withRef archName do
      elabCommand (← mkSpecDefCmd ref arch instr)
  -- Execute function
  let exeCmd ← mkExecuteCmd ref arch
  withRef archName do
    elabCommand exeCmd
  -- elaborator
  liftIO <| activeArchRef.set (some arch)

import MRiscX.ExtendParser.ExprDecoder
import Lean

open Lean
open Lean Elab Command

syntax (name := mkSpecsCmd)
  "mkSpecs " ident : command

private def joinLines (xs : List String) : String :=
  String.intercalate "\n" xs

private def trimAsciiStr (s : String) : String :=
  (s.trimAscii).toString

private def parseCommandStr (ref : Syntax) (s : String) : CommandElabM (TSyntax `command) := do
  match Parser.runParserCategory (← getEnv) `command s "<mkSpecs>" with
  | .ok stx =>
      pure ⟨stx⟩
  | .error err =>
      throwErrorAt ref s!"generated command failed:\n\n{s}\n\n{err}"

private def parserNameEq (n : Name) (expected : String) : Bool :=
  let txt := toString (n.eraseMacroScopes)
  txt == expected || txt.endsWith s!".{expected}"

private def isRegisterHole (h : DecodedHole) : Bool :=
  parserNameEq h.parser "register"

private def isImmediateHole (h : DecodedHole) : Bool :=
  parserNameEq h.parser "immediate"

private def isLabelHole (h : DecodedHole) : Bool :=
  parserNameEq h.parser "label"

private def isPunctuationTok (tok : String) : Bool :=
  tok == "," || tok == ";" || tok == ":" || tok == "." ||
  tok == ")" || tok == "]" || tok == "}"

private def isOpenBracketTok (tok : String) : Bool :=
  tok == "(" || tok == "[" || tok == "{"

private def instrTextOfCtor (ctor : DecodedCtor) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < ctor.pieces.size then
      let piece := ctor.pieces[i]
      let next? :=
        if hNext : i + 1 < ctor.pieces.size then
          some ctor.pieces[i + 1]
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
            let holeTxt :=
              if isRegisterHole h' then s!"x {nameTxt}" else nameTxt
            if addSpaceAfterHole then acc ++ holeTxt ++ " " else acc ++ holeTxt
      go (i + 1) acc
    else
      acc
  trimAsciiStr (go 0 "")

private def holesOfCtor (ctor : DecodedCtor) : Array DecodedHole :=
  ctor.pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push h

private def binderTypeText (h : DecodedHole) (hoareStyle : Bool) : String :=
  if hoareStyle then
    if isRegisterHole h then
      "UInt64"
    else if isImmediateHole h then
      "UInt64"
    else if isLabelHole h then
      "String"
    else
      h.tyText
  else
    h.tyText

private def mkBinderTexts (ctor : DecodedCtor) (hoareStyle : Bool) : Array String := Id.run do
  let mut names : Array Name := #[]
  let mut binders : Array String := #[]
  if hoareStyle then
    binders := binders.push "(P : Assertion)"
    binders := binders.push "(pc : UInt64)"
    names := names.push `P
    names := names.push `pc
  for h in holesOfCtor ctor do
    let n := h.name.eraseMacroScopes
    if !names.contains n then
      binders := binders.push s!"({n} : {binderTypeText h hoareStyle})"
      names := names.push n
  return binders

private def mkSpecBodyText (ctor : DecodedCtor) : (String × Bool) :=
  let raw := trimAsciiStr ctor.specText
  if raw.startsWith "⦃" then
    let instr := instrTextOfCtor ctor
    let instr := if instr.endsWith ";" then instr else instr ++ ";"
    (joinLines
      [s!"hoare ⟪{instr}⟫"
      ,raw
      ,"end"
      ], true)
  else
    (raw, false)

private def mkSpecDefCmd
    (ref : Syntax)
    (ctor : DecodedCtor) :
    CommandElabM (TSyntax `command) := do
  let specName := s!"specification_{ctor.ctorName.eraseMacroScopes}"
  let (body, hoareStyle) := mkSpecBodyText ctor
  let binders := String.intercalate " " (mkBinderTexts ctor hoareStyle).toList
  let cmdTxt := joinLines
    [s!"def {specName} {binders} : Prop :="
    ,s!"  {body}"
    ]
  let parsed? ←
    try
      pure (some (← parseCommandStr ref cmdTxt))
    catch _ =>
      pure none
  match parsed? with
  | some cmd =>
      pure cmd
  | none =>
      if hoareStyle then
        throwErrorAt ref
          "failed to elaborate generated Hoare specification. Make sure your file imports the Hoare elaborator and syntax modules before running `mkSpecs`."
      else
        throwErrorAt ref s!"failed to elaborate generated specification:\n{cmdTxt}"

def elabMkSpecs : CommandElab := fun stx => do
  match stx with
  | `(command| mkSpecs $archName:ident) => do
      let arch ← resolveArchFromIdent archName
      let nsName := s!"{arch.typeName.eraseMacroScopes}Specs"
      let nsCmd ← parseCommandStr archName.raw s!"namespace {nsName}"
      elabCommand nsCmd
      for ctor in arch.ctors do
        let cmd ← mkSpecDefCmd archName.raw ctor
        elabCommand cmd
      let endCmd ← parseCommandStr archName.raw s!"end {nsName}"
      elabCommand endCmd
  | _ =>
      throwUnsupportedSyntax

@[command_elab mkSpecsCmd]
def elabMkSpecsImpl : CommandElab :=
  elabMkSpecs

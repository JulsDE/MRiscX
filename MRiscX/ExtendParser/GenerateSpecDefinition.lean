import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.GenerateElaborator
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GenerateInstrSetHoareRewrite
import Lean

open Lean
open Lean Elab Command
open MRiscX.ExtendParser.CommandElabShared

namespace MRiscX.ExtendParser.GenerateSpecDefinition

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
      "RegisterName"
    else if isImmediateHole h then
      "UInt64"
    else if isLabelHole h then
      "String"
    else
      h.ty
  else
    h.ty

private def mkSpecBinderTexts
    (arch : ArchSpec)
    (spec : InstrSpec)
    (hoareStyle : Bool)
    (extraBinders : Array (Name × String) := #[]) :
    Array String := Id.run do
  let mut seen : Array Name := #[]
  let mut binders : Array String := #[]
  if hoareStyle then
    binders := binders.push s!"(P : MState {arch.typeName} → Prop)"
    binders := binders.push "(pc : ProgramCounter)"
    seen := seen.push `P
    seen := seen.push `pc
  for h in holesOfSpec spec do
    let n := h.name.eraseMacroScopes
    if !seen.contains n then
      binders := binders.push s!"({n} : {binderTypeText h hoareStyle})"
      seen := seen.push n
  for (n, tyTxt) in extraBinders do
    if !seen.contains n then
      binders := binders.push s!"({n} : {tyTxt})"
      seen := seen.push n
  return binders

private def termText (t : TSyntax `term) : String :=
  t.raw.reprint.getD (toString t.raw)

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def tokenizeLikeLeanIdent (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList do
    if isIdentChar c then
      cur := cur.push c
    else if !cur.isEmpty then
      out := out.push cur
      cur := ""
  if !cur.isEmpty then
    out := out.push cur
  return out

private def collectSomeIdentNamesFromText (s : String) : Array Name := Id.run do
  let toks := tokenizeLikeLeanIdent s
  let mut out : Array Name := #[]
  for i in [:toks.size] do
    if toks[i]! == "some" && i + 1 < toks.size then
      let n := Name.mkSimple toks[i + 1]!
      if !out.contains n then
        out := out.push n
  return out

private def mkProgramCounterBindersFromHoareTerms
    (terms : Array (TSyntax `term)) :
    Array (Name × String) := Id.run do
  let mut names : Array Name := #[]
  for t in terms do
    let found := collectSomeIdentNamesFromText (termText t)
    for n in found do
      if !names.contains n then
        names := names.push n
  let mut out : Array (Name × String) := #[]
  for n in names do
    out := out.push (n, "ProgramCounter")
  return out

private def mkInstrCtorArgText (h : Hole) : String :=
  let nameTxt := toString (h.name.eraseMacroScopes)
  nameTxt

private def instrCtorTextOfSpec (arch : ArchSpec) (spec : InstrSpec) : String :=
  let ctor := s!"{arch.typeName}.{spec.instrName.eraseMacroScopes}"
  let args := (holesOfSpec spec).toList.map mkInstrCtorArgText
  if args.isEmpty then
    ctor
  else
    s!"{ctor} {String.intercalate " " args}"

private def mkHoareSpecDefCmd
    (ref : Syntax)
    (arch : ArchSpec)
    (spec : InstrSpec)
    (specName : String)
    (pre l L_w L_b post : TSyntax `term)
    (origin : String := "<generated-spec>") :
    CommandElabM (TSyntax `command) := do
  let preTxt := termText pre
  let postTxt := termText post
  let lTxt := termText l
  let LwTxt := termText L_w
  let LbTxt := termText L_b
  let instrCtorTxt := instrCtorTextOfSpec arch spec
  let pcBinders := mkProgramCounterBindersFromHoareTerms #[pre, l, L_w, L_b, post]
  let binders := String.intercalate " " (mkSpecBinderTexts arch spec true pcBinders).toList
  let cmdTxt := joinLines
    [s!"def {specName} [runable_mstate : runable (MState {arch.typeName})]: Prop := ∀ {binders},"
    ,s!"  hoare_triple_up_1 (MState {arch.typeName}) {arch.typeName} (Code {arch.typeName}) RegisterName UInt64 ProgramCounter"
    ,s!"    (⧼{preTxt}⧽)"
    ,s!"    (⧼{postTxt}⧽)"
    ,s!"    ({lTxt})"
    ,s!"    ({LwTxt})"
    ,s!"    ({LbTxt})"
    ,s!"    ({instrCtorTxt})"
    ]
  parseCommandStr ref cmdTxt origin

def mkSpecDefCmds
    (ref : Syntax)
    (arch : ArchSpec)
    (spec : InstrSpec)
    (origin : String := "<generated-spec>") :
    CommandElabM (Array (TSyntax `command)) := do
  let baseSpecName := s!"specification_{spec.instrName.eraseMacroScopes}"
  let rawSpec := trimAsciiStr (spec.hoareDesc.raw.reprint.getD (toString spec.hoareDesc.raw))
  let raw := spec.hoareDesc.raw
  if raw.getKind == `instrSetSpecHoare then
    let args := raw.getArgs
    if _h : args.size = 14 then
      let pre : TSyntax `term := ⟨args[1]!⟩
      let l : TSyntax `term := ⟨args[3]!⟩
      let L_w : TSyntax `term := ⟨args[6]!⟩
      let L_b : TSyntax `term := ⟨args[8]!⟩
      let post : TSyntax `term := ⟨args[11]!⟩
      let tail := args[13]!
      let tailArgs := tail.getArgs
      if tailArgs.isEmpty then
        pure #[← mkHoareSpecDefCmd ref arch spec baseSpecName pre l L_w L_b post origin]
      else if _h2 : tailArgs.size = 14 then
        let pre2 : TSyntax `term := ⟨tailArgs[2]!⟩
        let l2 : TSyntax `term := ⟨tailArgs[4]!⟩
        let Lw2 : TSyntax `term := ⟨tailArgs[7]!⟩
        let Lb2 : TSyntax `term := ⟨tailArgs[9]!⟩
        let post2 : TSyntax `term := ⟨tailArgs[12]!⟩
        pure #[
          ← mkHoareSpecDefCmd ref arch spec (baseSpecName ++ "_true") pre l L_w L_b post origin,
          ← mkHoareSpecDefCmd ref arch spec (baseSpecName ++ "_false") pre2 l2 Lw2 Lb2 post2 origin
        ]
      else
        throwErrorAt spec.hoareDesc "invalid second hoare triple syntax in specification"
    else
      throwErrorAt spec.hoareDesc "invalid hoare specification syntax"
  else
    let binders := String.intercalate " " (mkSpecBinderTexts arch spec false).toList
    let cmdTxt := joinLines
      [s!"def {baseSpecName} {binders} : Prop :="
      ,s!"  {rawSpec}"
      ]
    pure #[← parseCommandStr ref cmdTxt origin]

end MRiscX.ExtendParser.GenerateSpecDefinition


syntax (name := mkSpecsCmd)
  "mkSpecs " ident : command

def elabMkSpecs : CommandElab := fun stx => do
  match stx with
  | `(command| mkSpecs $archName:ident) => do
      let some arch ← liftIO activeArchRef.get
        | throwErrorAt archName "no active architecture found; run `mkAll` or `mkElaborator` first"
      let expected := archName.getId.eraseMacroScopes
      if arch.name.eraseMacroScopes != expected then
        throwErrorAt archName s!"active architecture is `{arch.name}`, but `mkSpecs` was called for `{expected}`"
      let nsName := s!"{arch.typeName.eraseMacroScopes}Specs"
      let nsCmd ← parseCommandStr archName.raw s!"namespace {nsName}" "<mkSpecs>"
      withRef archName do
        elabCommand nsCmd
      for spec in arch.specs do
        for cmd in (← MRiscX.ExtendParser.GenerateSpecDefinition.mkSpecDefCmds archName.raw arch spec "<mkSpecs>") do
          withRef archName do
            elabCommand cmd
      let endCmd ← parseCommandStr archName.raw s!"end {nsName}" "<mkSpecs>"
      withRef archName do
        elabCommand endCmd
  | _ =>
      throwUnsupportedSyntax

@[command_elab mkSpecsCmd]
def elabMkSpecsImpl : CommandElab :=
  elabMkSpecs

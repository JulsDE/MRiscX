import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GenerateElaborator
import Lean

open Lean
open Lean Elab Command
open MRiscX.ExtendParser.CommandElabShared

syntax (name := mkSpecsCmd)
  "mkSpecs " ident : command

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

private def mkSpecDefCmd
    (ref : Syntax)
    (arch : ArchSpec)
    (spec : InstrSpec) :
    CommandElabM (TSyntax `command) := do
  let specName := s!"specification_{spec.instrName.eraseMacroScopes}"
  let rawSpec := trimAsciiStr (spec.hoareDesc.raw.reprint.getD (toString spec.hoareDesc.raw))
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
      parseCommandStr ref cmdTxt "<mkSpecs>"
  | _ =>
      let binders := String.intercalate " " (mkSpecBinderTexts arch spec false).toList
      let cmdTxt := joinLines
        [s!"def {specName} {binders} : Prop :="
        ,s!"  {rawSpec}"
        ]
      parseCommandStr ref cmdTxt "<mkSpecs>"

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
        withRef archName do
          elabCommand (← mkSpecDefCmd archName.raw arch spec)
      let endCmd ← parseCommandStr archName.raw s!"end {nsName}" "<mkSpecs>"
      withRef archName do
        elabCommand endCmd
  | _ =>
      throwUnsupportedSyntax

@[command_elab mkSpecsCmd]
def elabMkSpecsImpl : CommandElab :=
  elabMkSpecs

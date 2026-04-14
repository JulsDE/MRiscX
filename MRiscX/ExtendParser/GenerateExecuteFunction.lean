import MRiscX.ExtendParser.CommandElabShared

open Lean Elab Command



private def mkPatArgText (h : Hole) : String :=
  s!"({h.name} : {h.ty})"

private def mkAltLine (spec : InstrSpec) : String :=
  let ctor := toString spec.instrName
  let holes := MRiscX.ExtendParser.CommandElabShared.fieldsOfInputPieces spec.pieces
  let pat :=
    if holes.isEmpty then
      s!".{ctor}"
    else
      let args := String.intercalate " " (holes.toList.map mkPatArgText)
      s!".{ctor} {args}"
  s!"    | {pat} => ({spec.sem}) _ms"



def mkExecuteCmd
    (ref : Syntax)
    (arch : ArchSpec) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let execName := arch.execName
  let altLines := arch.specs.toList.map mkAltLine
  let cmdText := MRiscX.ExtendParser.CommandElabShared.joinLines <|
    [ s!"def {execName} (_ms : MState {typeName}) (_instr : {typeName}) : MState {typeName} :="
    , "  if _ms.terminated then _ms"
    , "  else"
    , "    match _instr with"
    ] ++
    altLines
  MRiscX.ExtendParser.CommandElabShared.parseCommandStr ref cmdText "<mkAll>"

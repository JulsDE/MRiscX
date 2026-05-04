import MRiscX.ExtendParser.CommandElabShared

open Lean Elab Command

private def sanitizeNameText (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    if c.isAlphanum then
      acc ++ String.singleton c
    else
      acc ++ "_"

private def semCheckName (arch : ArchSpec) (spec : InstrSpec) : String :=
  let archTxt := sanitizeNameText (toString arch.typeName)
  let ctorTxt := sanitizeNameText (toString spec.instrName)
  s!"generatedExecuteSemCheck_{archTxt}_{ctorTxt}"

private def mkPatArgText (h : Hole) : String :=
  s!"({h.name} : {h.ty})"

private def mkSemCheckCmd
    (arch : ArchSpec)
    (spec : InstrSpec) :
    CommandElabM (TSyntax `command) := do
  let helper := semCheckName arch spec
  let semTxt := spec.sem.raw.reprint.getD (toString spec.sem.raw)
  let holes := MRiscX.ExtendParser.CommandElabShared.fieldsOfInputPieces spec.pieces
  let holeBinders :=
    if holes.isEmpty then
      ""
    else
      " " ++ String.intercalate " " (holes.toList.map mkPatArgText)
  let cmdText := MRiscX.ExtendParser.CommandElabShared.joinLines
    [ s!"private def {helper}{holeBinders} : MState {arch.typeName} → MState {arch.typeName} :="
    , s!"  {semTxt}"
    ]
  MRiscX.ExtendParser.CommandElabShared.parseCommandStr spec.sem.raw cmdText "<mkAll>"

private def mkAltLine (_arch : ArchSpec) (spec : InstrSpec) : String :=
  let ctor := toString spec.instrName
  let holes := MRiscX.ExtendParser.CommandElabShared.fieldsOfInputPieces spec.pieces
  let pat :=
    if holes.isEmpty then
      s!".{ctor}"
    else
      let args := String.intercalate " " (holes.toList.map mkPatArgText)
      s!".{ctor} {args}"
  s!"    | {pat} => ({spec.sem.raw.reprint.getD (toString spec.sem.raw)}) _ms"

private def mkExecuteMainCmd
    (ref : Syntax)
    (arch : ArchSpec) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let execName := arch.execName
  let altLines := arch.specs.toList.map (mkAltLine arch)
  let cmdText := MRiscX.ExtendParser.CommandElabShared.joinLines <|
    [ s!"def {execName} (_ms : MState {typeName}) (_instr : {typeName}) : MState {typeName} :="
    , "  if _ms.terminated then _ms"
    , "  else"
    , "    match _instr with"
    ] ++
    altLines
  MRiscX.ExtendParser.CommandElabShared.parseCommandStr ref cmdText "<mkAll>"

def mkExecuteCmds
    (ref : Syntax)
    (arch : ArchSpec) :
    CommandElabM (Array (TSyntax `command)) := do
  let mut cmds : Array (TSyntax `command) := #[]
  for spec in arch.specs do
    cmds := cmds.push (← mkSemCheckCmd arch spec)
  cmds := cmds.push (← mkExecuteMainCmd ref arch)
  pure cmds

import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.Elab.HandleNumOrIdent
import MRiscX.Elab.HandleRegister
import Lean

open Lean
open Lean Elab Command
open Lean PrettyPrinter
open MRiscX.ExtendParser.CommandElabShared

namespace MRiscX.ExtendParser.GenerateDelaborator

def SyntaxInstrMap := TMap UInt64 (TSyntax `mriscx_Instr)
deriving Repr, Inhabited

private def trimAsciiStr (s : String) : String :=
  (s.trimAscii).toString

private def parseUInt64FromText? (s : String) : Option UInt64 := Id.run do
  let txt := trimAsciiStr s
  if txt.isEmpty then
    return none
  match txt.toNat? with
  | some n =>
      return some n.toUInt64
  | none =>
      return none

private def parseUInt64Key? (t : TSyntax `term) : Option UInt64 :=
  match t with
  | `(term| UInt64.ofNat $n:num) =>
      some n.getNat.toUInt64
  | `(term| $n:num) =>
      some n.getNat.toUInt64
  | _ =>
      parseUInt64FromText? (t.raw.reprint.getD (toString t.raw))

private def parseLabelKey? (t : TSyntax `term) : Option String :=
  match t with
  | `(term| $s:str) =>
      some s.getString
  | `(term| $i:ident) =>
      some i.getId.eraseMacroScopes.toString
  | _ =>
      none

private def parseRegisterIndexFromName? (s : String) : Option Nat :=
  let s := trimAsciiStr s
  if s.startsWith "x" then
    let rest := trimAsciiStr ((s.drop 1).toString)
    rest.toNat?
  else
    none

private def mkRegisterSyntaxFromNat (n : Nat) : UnexpandM (TSyntax `register) := do
  let nStx : TSyntax `num := ⟨Syntax.mkNumLit (toString n)⟩
  `(register| x $nStx:num)

def registerFromTerm (t : TSyntax `term) : UnexpandM (TSyntax `register) := do
  try
    getRegisterTerm t
  catch _ =>
    match t with
    | `(term| RegisterName.mk (RegisterNr.ofNat $n:num) $_) =>
        `(register| x $n:num)
    | `(term| RegisterName.mk (RegisterNr.ofUInt64 $nTerm) $_) =>
        let some n := parseUInt64Key? nTerm
          | throw ()
        mkRegisterSyntaxFromNat n.toNat
    | `(term| { nr := RegisterNr.ofNat $n:num, name := $_ }) =>
        `(register| x $n:num)
    | `(term| { nr := RegisterNr.ofUInt64 $nTerm, name := $_ }) =>
        let some n := parseUInt64Key? nTerm
          | throw ()
        mkRegisterSyntaxFromNat n.toNat
    | `(term| RegisterName.mk $_ $nameTerm) =>
        match nameTerm with
        | `(term| $name:str) =>
            let some n := parseRegisterIndexFromName? name.getString
              | throw ()
            mkRegisterSyntaxFromNat n
        | _ =>
            throw ()
    | `(term| { nr := $_, name := $nameTerm }) =>
        match nameTerm with
        | `(term| $name:str) =>
            let some n := parseRegisterIndexFromName? name.getString
              | throw ()
            mkRegisterSyntaxFromNat n
        | _ =>
            throw ()
    | _ =>
        throw ()

partial def termToInstrMapWith
    (termToInstr : TSyntax `term → UnexpandM (TSyntax `mriscx_Instr))
    (t : TSyntax `term) :
    UnexpandM SyntaxInstrMap := do
  match t with
  | `(term| TMap.empty $d) =>
      let defaultInstr ← termToInstr d
      pure (TMap.empty defaultInstr)
  | `(term| TMap.put $k $v $m) =>
      let some key := parseUInt64Key? k
        | throw ()
      let instr ← termToInstr v
      let rest ← termToInstrMapWith termToInstr m
      pure (TMap.put key instr rest)
  | `(term| ($k ↦ $v ; $m)) =>
      let some key := parseUInt64Key? k
        | throw ()
      let instr ← termToInstr v
      let rest ← termToInstrMapWith termToInstr m
      pure (TMap.put key instr rest)
  | `(term| id $x) =>
      termToInstrMapWith termToInstr x
  | _ =>
      throw ()

partial def termToLabelMap (t : TSyntax `term) : Option LabelMap :=
  match t with
  | `(term| PMap.empty) =>
      some PMap.empty
  | `(term| EmptyLabelMap) =>
      some PMap.empty
  | `(term| PMap.put $k $v $m) =>
      match parseLabelKey? k, parseUInt64Key? v, termToLabelMap m with
      | some label, some pc, some rest =>
          some (PMap.put label pc rest)
      | _, _, _ =>
          none
  | `(p($k:str ↦ UInt64.ofNat $v:num ; $m)) =>
      match termToLabelMap ⟨m⟩ with
      | some rest =>
          some (PMap.put k.getString v.getNat.toUInt64 rest)
      | none =>
          none
  | `(p($k:str ↦ $v:num ; $m)) =>
      match termToLabelMap ⟨m⟩ with
      | some rest =>
          some (PMap.put k.getString v.getNat.toUInt64 rest)
      | none =>
          none
  | `(term| id $x) =>
      termToLabelMap x
  | _ =>
      none

private def getInstrAt? (instructionMap : SyntaxInstrMap) (k : UInt64) :
    Option (TSyntax `mriscx_Instr) :=
  if instructionMap.getKeys.contains k then
    some (instructionMap.get k)
  else
    none

private def getInstrKeys (instructionMap : SyntaxInstrMap) : List UInt64 :=
  instructionMap.getKeys

private def getInstrLastKey? (instructionMap : SyntaxInstrMap) : Option UInt64 :=
  instructionMap.getLastKey

def createLabelInstructionArray (instructionMap : SyntaxInstrMap) (labelMap : LabelMap) :
    Array (String × Array (TSyntax `mriscx_Instr)) := Id.run do
  let labels := labelMap.getKeys
  if labels.length == 1 then
    let resultLbl := labels.head!
    let mut resultInstrs := #[]
    for keyInstr in getInstrKeys instructionMap do
      match getInstrAt? instructionMap keyInstr with
      | some instr =>
          resultInstrs := resultInstrs.push instr
      | none =>
          pure ()
    return #[(resultLbl, resultInstrs)]

  let mut result := #[]
  for i in [0:labels.length] do
    let labelEntry := labels.get!Internal i
    let labelEntryPlusOne := labels.get?Internal (i + 1)
    match labelEntryPlusOne with
    | some labelPlusOne =>
        let curIndex := labelMap.get labelEntry
        let nextIndex := labelMap.get labelPlusOne
        let mut curInstrs := #[]
        match curIndex, nextIndex with
        | some cur, some next =>
            for j in [cur.toNat:next.toNat] do
              match getInstrAt? instructionMap (id j.toUInt64) with
              | some instr =>
                  curInstrs := curInstrs.push instr
              | none =>
                  pure ()
            result := result.push (labelEntry, curInstrs)
        | _, _ =>
            pure ()
    | none =>
        let curIndex := labelMap.get labelEntry
        let lastIndex := getInstrLastKey? instructionMap
        let mut curInstrs := #[]
        match curIndex, lastIndex with
        | some cur, some last =>
            for j in [cur.toNat:last.toNat + 1] do
              match getInstrAt? instructionMap (id j.toUInt64) with
              | some instr =>
                  curInstrs := curInstrs.push instr
              | none =>
                  pure ()
            result := result.push (labelEntry, curInstrs)
        | _, _ =>
            pure ()
  return result

private def holeNameText (h : Hole) : String :=
  toString (h.name.eraseMacroScopes)

private def holeSynNameText (h : Hole) : String :=
  s!"{holeNameText h}Syn"

private def holeCategoryText? (h : Hole) : Option String :=
  let p := h.parser
  if parserTextEq p "register" then
    some "register"
  else if parserTextEq p "immediate" then
    some "num_or_ident"
  else if parserTextEq p "label" then
    some "label"
  else
    none

private def sanitizeTagText (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    if c.isAlphanum then
      acc ++ String.singleton c
    else
      acc ++ "_"

private def tagFromName (n : Name) : String :=
  sanitizeTagText (toString (n.eraseMacroScopes))

private def helperNameText (arch : ArchSpec) (suffix : String) : Name :=
  Name.mkSimple s!"generatedDelab_{tagFromName arch.name}_{suffix}"

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

private def holeInfos (spec : InstrSpec) : Array (Hole × Bool) := Id.run do
  let mut infos : Array (Hole × Bool) := #[]
  let mut prevLitTok : Option String := none
  for piece in spec.pieces do
    match piece with
    | .lit tok =>
        prevLitTok := some tok
    | .hole h =>
        infos := infos.push (h, prevLitTok == some ".")
        prevLitTok := none
  return infos

private def mkInstrPatternText (ctorText : String) (holes : Array Hole) : String :=
  if holes.isEmpty then
    ctorText
  else
    let holePats := holes.toList.map (fun h => s!"${holeNameText h}")
    String.intercalate " " (ctorText :: holePats)

private def mkInstrSyntaxText (spec : InstrSpec) : CommandElabM String := do
  let mut parts : List String := []
  for piece in spec.pieces do
    match piece with
    | .lit tok =>
        parts := parts ++ [tok]
    | .hole h =>
        match holeCategoryText? h with
        | some cat =>
            parts := parts ++ [s!"${holeSynNameText h}:{cat}"]
        | none =>
            throwError s!"unsupported placeholder parser `{h.parser}` in instruction `{spec.instrName.eraseMacroScopes}`"
  pure (String.intercalate " " parts)

private def mkInstrAltLines
    (arch : ArchSpec)
    (labelFromTermFn : Name)
    (spec : InstrSpec) :
    CommandElabM (List String) := do
  let holes := fieldsOfInputPieces spec.pieces
  let holeInfoMap := holeInfos spec
  let mut parseLines : List String := []
  for idx in [0:holes.size] do
    let h := holes[idx]!
    let synName := holeSynNameText h
    if parserTextEq h.parser "register" then
      parseLines := parseLines ++ [s!"      let {synName} ← MRiscX.ExtendParser.GenerateDelaborator.registerFromTerm {holeNameText h}"]
    else if parserTextEq h.parser "immediate" then
      parseLines := parseLines ++ [s!"      let {synName} ← numOrIdentToSyntax {holeNameText h}"]
    else if parserTextEq h.parser "label" then
      let withDot := if idx < holeInfoMap.size then (holeInfoMap[idx]!).2 else false
      let withDotTxt := if withDot then "true" else "false"
      parseLines := parseLines ++ [s!"      let {synName} ← {labelFromTermFn} {holeNameText h} {withDotTxt}"]
    else
      throwError s!"unsupported placeholder parser `{h.parser}` in instruction `{spec.instrName.eraseMacroScopes}`"

  let ctorText := toString (qualifyCtorName arch.typeName spec.instrName)
  let patText := mkInstrPatternText ctorText holes
  let syntaxText ← mkInstrSyntaxText spec
  pure <|
    [ s!"  | `(term| {patText}) => do" ] ++
    parseLines ++
    [ s!"      `(mriscx_Instr| {syntaxText};)" ]

def mkDelaboratorCmds
    (ref : Syntax)
    (arch : ArchSpec) :
    CommandElabM (Array (TSyntax `command)) := do
  let labelFromTermFn := helperNameText arch "labelFromTerm"
  let termToInstrFn := helperNameText arch "termToInstr"
  let codeUnexpanderFn := helperNameText arch "codeUnexpander"

  let mut instrAltLines : List String := []
  for spec in arch.specs do
    instrAltLines := instrAltLines ++ (← mkInstrAltLines arch labelFromTermFn spec)

  let labelFnCmdText := joinLines
    [ s!"private def {labelFromTermFn} (t : Lean.TSyntax `term) (withDot : Bool) : Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `label) := do"
    , "  match t with"
    , "  | `(term| $i:ident) =>"
    , "      `(label| $i:ident)"
    , "  | `(term| $s:str) =>"
    , "      let raw := s.getString"
    , "      let raw := if withDot && raw.startsWith \".\" then raw.drop 1 else raw"
    , "      if raw.isEmpty then throw () else"
    , "      `(label| $(Lean.mkIdent raw.toName):ident)"
    , "  | _ => throw ()"
    ]

  let termToInstrCmdText := joinLines <|
    [ s!"private def {termToInstrFn} (t : Lean.TSyntax `term) : Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `mriscx_Instr) := do"
    , "  match t with"
    ] ++ instrAltLines ++
    [ "  | _ => throw ()" ]

  let codeUnexpanderCmdText := joinLines
    [ s!"@[app_unexpander Code.mk]"
    , s!"def {codeUnexpanderFn} : Lean.PrettyPrinter.Unexpander"
    , "  | `(term| $_ $labelMapTerm $instrMapTerm) => do"
    , "      let some labels := MRiscX.ExtendParser.GenerateDelaborator.termToLabelMap labelMapTerm | throw ()"
    , s!"      let instructionMap ← MRiscX.ExtendParser.GenerateDelaborator.termToInstrMapWith {termToInstrFn} instrMapTerm"
    , "      let syntaxArray := MRiscX.ExtendParser.GenerateDelaborator.createLabelInstructionArray instructionMap labels"
    , "      if syntaxArray.size > 0 then"
    , "        let mut syntaxes := #[]"
    , "        for labelWithCode in syntaxArray do"
    , "          let mut instrSyntaxes := #[]"
    , "          for instr in labelWithCode.2 do"
    , "            instrSyntaxes := instrSyntaxes.push (←`(mriscx_Instr| $instr))"
    , "          let labelName := Lean.mkIdent labelWithCode.1.toName"
    , "          syntaxes := syntaxes.push (←`(mriscx_label| $labelName:ident : $instrSyntaxes*))"
    , "        `(mriscx_syntax| mriscx"
    , "          $syntaxes*"
    , "          end)"
    , "      else"
    , "        throw ()"
    , "  | _ => throw ()"
    ]

  let labelFnCmd ← parseCommandStr ref labelFnCmdText "<mkDelaborator>"
  let termToInstrCmd ← parseCommandStr ref termToInstrCmdText "<mkDelaborator>"
  let codeUnexpanderCmd ← parseCommandStr ref codeUnexpanderCmdText "<mkDelaborator>"
  pure #[labelFnCmd, termToInstrCmd, codeUnexpanderCmd]

end MRiscX.ExtendParser.GenerateDelaborator

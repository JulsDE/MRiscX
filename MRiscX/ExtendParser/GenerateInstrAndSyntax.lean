import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateInstrToExpr
import MRiscX.Hoare.HoareAssignmentElab
import MRiscX.ExtendParser.GenerateElaborator
import Mathlib.Data.Set.Basic

import Lean

open Lean
open Lean Elab Command
open Lean.Parser.Command
open Lean.Parser.Term

/-
  Placeholders used in instruction syntax signatures.
-/



/-! Helpers -/

private partial def leafTokenText? : Syntax → Option String
  | Syntax.ident _ rawVal _ _ =>
      some (toString rawVal)
  | Syntax.atom _ val =>
      some val
  | Syntax.node _ _ args =>
      let rec go (i : Nat) : Option String :=
        if h : i < args.size then
          match leafTokenText? (args[i]'h) with
          | some s => some s
          | none   => go (i + 1)
        else
          none
      go 0
  | Syntax.missing =>
      none

private def joinLines (xs : List String) : String :=
  String.intercalate "\n" xs

private def parseCommandStr (ref : Syntax) (s : String) : CommandElabM (TSyntax `command) := do
  match Parser.runParserCategory (← getEnv) `command s "<mkInstrSet>" with
  | .ok stx =>
      pure ⟨stx⟩
  | .error err =>
      throwErrorAt ref s!"generated command failed:\n\n{s}\n\n{err}"

private def trimAsciiLocal (s : String) : String :=
  (s.trimAscii).toString

private def numOrIdentAsTerm (s : TSyntax `num_or_ident) : TermElabM (TSyntax `term) := do
  match s with
  | `(num_or_ident| $n:num) =>
      `(term| $n:num)
  | `(num_or_ident| $i:ident) =>
      `(term| $i:ident)
  | _ =>
      throwError "unsupported num_or_ident in instruction-set hoare assignment"

private def registerIndexAsTerm (r : TSyntax `register) : TermElabM (TSyntax `term) := do
  if let some reg := getCorrespondingRegisterName? r then
    let n : TSyntax `num := Syntax.mkNumLit s!"{reg.nr}"
    `(term| $n:num)
  else
    match r with
    | `(register| x $i:num_or_ident) =>
        numOrIdentAsTerm i
    | _ =>
        throwError "unsupported register in instruction-set hoare assignment"

private def mkRegisterNameFromIdx (idx : TSyntax `term) : TermElabM (TSyntax `term) := do
  `(term| RegisterName.mk (RegisterNr.ofUInt64 $idx:term) (@toString UInt64 instToStringUInt64 $idx:term))

private partial def replaceInstrSetKeywords (stx : Term) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  go stx
where
  go : Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
      `(term| ($stateTerm:term).terminated)
  | _stx@`(⸨pc⸩) =>
      `(term| ($stateTerm:term).pc)
  | stx =>
      match stx with
      | .node _ k args => do
          let args ← args.mapM go
          return .node (.fromRef stx (canonical := true)) k args
      | _ => pure stx

private partial def getInstrSetAssignmentArray
    (stx : TSyntax `instr_set_hoare_assignment_chain)
    (curArr : Array (TSyntax `instr_set_hoare_assignment)) :
    TermElabM (Array (TSyntax `instr_set_hoare_assignment)) := do
  match stx with
  | `(instr_set_hoare_assignment_chain| $t:instr_set_hoare_assignment) =>
      return curArr.push t
  | `(instr_set_hoare_assignment_chain| $t1:instr_set_hoare_assignment ; $t2:instr_set_hoare_assignment) =>
      return (curArr.push t1).push t2
  | `(instr_set_hoare_assignment_chain| $t:instr_set_hoare_assignment ; $s:instr_set_hoare_assignment_chain) =>
      return (← getInstrSetAssignmentArray s (curArr.push t))
  | _ =>
      throwError "unknown instruction-set hoare assignment chain"

private def foldInstrSetAssignment
    (element : TSyntax `instr_set_hoare_assignment)
    (curTerm : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match element with
  | `(instr_set_hoare_assignment| x[$r:num_or_ident] ← $t:term)
  | `(instr_set_hoare_assignment| x[$r:num_or_ident] <- $t:term) => do
      let idx ← numOrIdentAsTerm r
      let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $reg $newT)
  | `(instr_set_hoare_assignment| x[$r:register] ← $t:term)
  | `(instr_set_hoare_assignment| x[$r:register] <- $t:term) => do
      let idx ← registerIndexAsTerm r
      let reg ← mkRegisterNameFromIdx idx
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addRegisterAt ($curTerm) $reg $newT)
  | `(instr_set_hoare_assignment| mem[$m:term] ← $t:term)
  | `(instr_set_hoare_assignment| mem[$m:term] <- $t:term) => do
      let newM : TSyntax `term := ⟨← replaceInstrSetKeywords m curTerm⟩
      let newT : TSyntax `term := ⟨← replaceInstrSetKeywords t curTerm⟩
      `(term| MState.addMemory ($curTerm) $newM $newT)
  | `(instr_set_hoare_assignment| pc++) =>
      `(term| MState.incInstrCounter (MState.incPc ($curTerm)))
  | `(instr_set_hoare_assignment| $pc:ident ++)
    =>
      if pc.getId == `pc then
        `(term| MState.incInstrCounter (MState.incPc ($curTerm)))
      else
        throwError "only `pc++` is supported in instruction-set hoare assignment"
  | `(instr_set_hoare_assignment| $pc:ident ← $i:term)
  | `(instr_set_hoare_assignment| $pc:ident <- $i:term) =>
      if pc.getId == `pc then
        `(term| MState.incInstrCounter (MState.setPc ($curTerm) $i:term))
      else
        throwError "only `pc <- ...` is supported in instruction-set hoare assignment"
  | _ =>
      throwError "unknown instruction-set hoare assignment element"

private def generateInstrSetAssignmentSyntax
    (hChain : TSyntax `instr_set_hoare_assignment_chain)
    (stateTerm : TSyntax `term) : TermElabM Syntax := do
  let termArray ← getInstrSetAssignmentArray hChain #[]
  let result : TSyntax `term ← termArray.foldrM foldInstrSetAssignment stateTerm
  pure result.raw

private partial def rewriteInstrSetAssignmentTerms (stx : Syntax) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  withFreshMacroScope do
    go stx
where
  go : Syntax → TermElabM Syntax
  | _stx@`(term| ⟦⟧) =>
      return stateTerm.raw
  | _stx@`(term| ⟦$h:instr_set_hoare_assignment_chain⟧) => do
      return (← generateInstrSetAssignmentSyntax h stateTerm)
  | stx =>
      match stx with
      | .node _ k args => do
          let args ← args.mapM go
          return .node (.fromRef stx (canonical := true)) k args
      | _ => pure stx

private def processInstrSetHoareTerm (stx : Term) (stateTerm : TSyntax `term) : TermElabM Syntax := do
  let rewritten ← rewriteInstrSetAssignmentTerms stx.raw stateTerm
  replaceInstrSetKeywords ⟨rewritten⟩ stateTerm

private partial def elabInstrSetHoareTerm (stx : Term) : TermElabM Term := do
  let stId : TSyntax `ident := mkIdent `st
  let stTerm : TSyntax `term ← `(term| $stId:ident)
  let newStx ← processInstrSetHoareTerm stx stTerm
  return (← `(term| fun $stId:ident => ($(⟨newStx⟩))))

elab "⧼" t:term "⧽" : term => do
  let newT ← elabInstrSetHoareTerm t
  return (← Lean.Elab.Term.elabTerm (← `(term| $newT:term)) none)

private def parserTextEq (p : String) (expected : String) : Bool :=
  p == expected || p.endsWith s!".{expected}"

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
      parseCommandStr Syntax.missing cmdTxt
  | _ =>
      let binders := String.intercalate " " (mkSpecBinderTexts arch spec false).toList
      let cmdTxt := joinLines
        [s!"def {specName} {binders} : Prop :="
        ,s!"  {rawSpec}"
        ]
      parseCommandStr Syntax.missing cmdTxt


/-! Parse DSL into persisted specs -/

private def fieldsOfInputPieces (pieces : Array Piece) : Array Hole :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _    => acc
    | .hole h   => acc.push h

private def ensureNoDuplicateFieldNames
    (ctorName : Name)
    (fields : Array Hole) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for h in fields do
    let n := h.name.eraseMacroScopes
    if seen.contains n then
      throwError s!"duplicate placeholder name `{n}` in constructor `{ctorName}`"
    seen := seen.push n

private def elabPiece (piece : TSyntax `instr_set_piece) : CommandElabM Piece := do
  match piece with
  | `(instr_set_piece| $h:instr_set_hole) =>
      match h with
      | `(instr_set_hole| ($name:ident : $parser:stx)) =>
          let n := name.getId.eraseMacroScopes
          match parser with
          | `(stx | register) =>
              pure <| .hole { name := n, ty := "RegisterName", parser := "register" }
          | `(stx | label) =>
              pure <| .hole { name := n, ty := "String", parser := "label" }
          | `(stx | immediate) =>
              pure <| .hole { name := n, ty := "UInt64", parser := "immediate" }
          | _ =>
              throwErrorAt parser "unknown hole parser category (expected register | immediate | label)"
      | _ =>
          throwErrorAt h "invalid placeholder"
  | _ =>
      match leafTokenText? piece.raw with
      | some tok =>
          pure <| .lit tok
      | none =>
          throwErrorAt piece "failed to reconstruct token text"

private def extractPieces
    (sig : TSyntax `instr_set_sig) :
    CommandElabM (Array Piece) := do
  match sig with
  | `(instr_set_sig| $[$pieces:instr_set_piece]*) =>
      pieces.mapM elabPiece
  | _ =>
      throwErrorAt sig "invalid syntax signature"

private def mkCtorSpec
    (entry : TSyntax `instr_set_entry) :
    CommandElabM InstrSpec := do
  match entry with
  | `(instr_set_entry| $ctorName:ident : { syntax : $sig:instr_set_sig, semantics : $sem:term, specification : $spec:instr_set_spec }) => do
      let pieces ← extractPieces sig
      let holes := fieldsOfInputPieces pieces
      let ctorName := ctorName.getId.eraseMacroScopes
      let arch : InstrSpec := {
          instrName := ctorName,
          ref := entry.raw.reprint.getD (toString entry.raw),
          pieces := pieces,
          sem := sem.raw.reprint.getD (toString sem.raw),
          hoareDesc := spec

      }
      ensureNoDuplicateFieldNames ctorName holes
      return arch
  | _ =>
      throwErrorAt entry "invalid instruction entry"


/-! Code generation from persisted ArchSpec -/

private def fieldsOfDecodedPieces (pieces : Array Piece) : Array Hole :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push h

private def mkCtorTypeText (typeName : Name) (holes : Array Hole) : String :=
  let resultTy := toString typeName
  if holes.isEmpty then
    resultTy
  else
    let argTys := holes.toList.map (fun h => h.ty)
    String.intercalate " → " (argTys ++ [resultTy])

private def mkCtorLine (typeName : Name) (spec : InstrSpec) : String :=
  let ctor := toString spec.instrName
  let ty := mkCtorTypeText typeName (fieldsOfDecodedPieces spec.pieces)
  s!"  | {ctor} : {ty}"

private def mkInductiveCmd
    (arch : ArchSpec) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let ctorLines := arch.specs.toList.map (mkCtorLine typeName)
  let cmdText := joinLines <|
    [s!"inductive {typeName} : Type where"] ++
    ctorLines ++
    ["deriving Repr, BEq, Inhabited"]
  parseCommandStr Syntax.missing cmdText

private def mkPatArgText (h : Hole) : String :=
  s!"({h.name} : {h.ty})"

private def mkAltLine (spec : InstrSpec) : String :=
  let ctor := toString spec.instrName
  let holes := fieldsOfDecodedPieces spec.pieces
  let pat :=
    if holes.isEmpty then
      s!".{ctor}"
    else
      let args := String.intercalate " " (holes.toList.map mkPatArgText)
      s!".{ctor} {args}"
  s!"  | {pat} => ({spec.sem}) _ms"



private def mkExecuteCmd
    (arch : ArchSpec) :
    CommandElabM (TSyntax `command) := do
  let typeName := arch.typeName
  let execName := arch.execName
  let altLines := arch.specs.toList.map mkAltLine
  let cmdText := joinLines <|
    [ s!"def {execName} (_ms : MState {typeName}) (_instr : {typeName}) : MState {typeName} :="
    , "  match _instr with"
    ] ++
    altLines
  parseCommandStr Syntax.missing cmdText

/-! Elaborators -/

def tres (stx : TSyntax `instr_set_spec) : CommandElabM (TSyntax `term) := do
  return ⟨stx⟩




-- @[command_elab mkTypeCmd]
-- def elabMkTypeImpl : CommandElab :=
--   elabMkType

-- @[command_elab mkExecutionCmd]
-- def elabMkExecutionImpl : CommandElab :=
--   elabMkExecution



elab "mkAll " archName:ident typeName:ident execName:ident entries:instr_set_entry*: command => do
  let specs ← (entries.mapM mkCtorSpec)
  let arch : ArchSpec := {
    name     := archName.getId.eraseMacroScopes
    typeName := typeName.getId.eraseMacroScopes
    execName := execName.getId.eraseMacroScopes
    specs    := specs
  }
  let indCmd ← mkInductiveCmd arch
  for instr in arch.specs do
    let syn ← mkSyntaxCmdForCtor instr
    elabCommand syn
  logInfo s!"Created type {arch.typeName} for {arch.name}"
  -- logInfo s!"{arch.specs[0]!.hoareDesc}"
  elabCommand indCmd
  elabCommand (← mkGetInstrExprCmd arch)
  elabCommand (← mkTest)
  for instr in arch.specs do
    elabCommand (← mkSpecDefCmd arch instr)
  -- `mkTest` may emit extra elaborators/commands; keep it opt-in at call sites.
  -- elabCommand (← mkTest)
  let exeCmd ← mkExecuteCmd arch
  elabCommand exeCmd
  liftIO <| activeArchRef.set (some arch)
  -- let ad : TSyntax `term ← tres arch.specs[0]!.hoareDesc
  -- elabCommand (←`(#check $ad))

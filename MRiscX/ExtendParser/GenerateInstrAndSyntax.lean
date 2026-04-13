import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.ExprDecoder
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateInstrToExpr
import MRiscX.Hoare.HoareAssignmentElab
-- import MRiscX.ExtendParser.GenerateElaborator
import Mathlib.Data.Set.Basic

import Lean

open Lean
open Lean Elab Command
open Lean.Parser.Command
open Lean.Parser.Term

/-
  Placeholders used in instruction syntax signatures.
-/


syntax num : num_or_ident
syntax ident : num_or_ident

syntax &"x" num_or_ident : register
syntax "x0" : register

syntax num_or_ident : immediate
syntax ident : label

declare_syntax_cat instr_set_hoare_assignment
declare_syntax_cat instr_set_hoare_assignment_chain
declare_syntax_cat instr_set_hoare_assignment_term

syntax "x[" num_or_ident "]" "←" term : instr_set_hoare_assignment
syntax "x[" num_or_ident "]" "<-" term : instr_set_hoare_assignment
syntax "x[" register "]" "←" term : instr_set_hoare_assignment
syntax "x[" register "]" "<-" term : instr_set_hoare_assignment
syntax "mem[" term &"]" "←" term : instr_set_hoare_assignment
syntax "mem[" term &"]" "<-" term : instr_set_hoare_assignment
syntax ident "++" : instr_set_hoare_assignment
syntax ident "←" term : instr_set_hoare_assignment
syntax ident "<-" term : instr_set_hoare_assignment

syntax "⟦⟧" : instr_set_hoare_assignment_term
syntax instr_set_hoare_assignment : instr_set_hoare_assignment_chain
syntax instr_set_hoare_assignment ";" instr_set_hoare_assignment : instr_set_hoare_assignment_chain
syntax instr_set_hoare_assignment ";" instr_set_hoare_assignment_chain : instr_set_hoare_assignment_chain
syntax "⟦" instr_set_hoare_assignment_chain "⟧" : instr_set_hoare_assignment_term

syntax "⟦⟧" : term
syntax "⟦" instr_set_hoare_assignment_chain "⟧" : term
syntax "x[" register "]" : term
syntax "x[" num_or_ident "]" : term
syntax "mem[" term "]" : term
syntax "labels[" ident "]" : term
syntax "labels[" &"." ident "]" : term
syntax "⸨pc⸩" : term
syntax "⸨terminated⸩": term

declare_syntax_cat instr_set_hole
syntax register : instr_set_hole
syntax immediate : instr_set_hole
syntax label : instr_set_hole
syntax "(" ident ":" stx ")" : instr_set_hole

declare_syntax_cat instr_set_piece
syntax instr_set_hole : instr_set_piece
syntax ident : instr_set_piece
syntax num   : instr_set_piece
syntax str   : instr_set_piece
syntax char  : instr_set_piece
syntax ","   : instr_set_piece
syntax ";"   : instr_set_piece
syntax ":"   : instr_set_piece
syntax "."   : instr_set_piece
syntax "+"   : instr_set_piece
syntax "-"   : instr_set_piece
syntax "*"   : instr_set_piece
syntax "/"   : instr_set_piece
syntax "="   : instr_set_piece
syntax "<"   : instr_set_piece
syntax ">"   : instr_set_piece
syntax "<="  : instr_set_piece
syntax ">="  : instr_set_piece

declare_syntax_cat instr_set_sig
syntax ((!( ("," "semantics" ":") )) instr_set_piece)+ : instr_set_sig

declare_syntax_cat instr_set_spec
-- syntax instr_set_spec : term
syntax "⦃" term "⦄" term "↦" "⟨" term "|" term "⟩" "⦃" term "⦄" : instr_set_spec
syntax ((!("⦃")) term) : instr_set_spec

declare_syntax_cat instr_set_entry
syntax ident ":" "{"
  "syntax" ":" instr_set_sig ","
  "semantics" ":" term ","
  "specification" ":" instr_set_spec
  "}" : instr_set_entry
syntax ident ":" "{"
  "syntax" ":" instr_set_sig ","
  "semantics" ":" term
  ppLine "specification" ":" instr_set_spec
  "}" : instr_set_entry

syntax (name := mkInstrSetTerm)
  "mkInstrSet " ident ident ident ppLine withPosition((colGe instr_set_entry)+) : term

syntax (name := mkTypeCmd)
  "mkType " ident : command

syntax (name := mkExecutionCmd)
  "mkExecution " ident : command





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

def adf (name : Name) : CommandElabM (TSyntax `ident) := do
  let n := mkIdent name
  return ⟨n⟩







private def mkCtorPattern (ctorName : TSyntax `ident) (fields : Array (TSyntax `ident × TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  let argPats ← fields.mapM fun (name, _) => `(term| $name:ident)
  if argPats.isEmpty then
    `(term| .$ctorName:ident)
  else
    `(term| .$ctorName:ident $argPats*)

private def mkMStateEndoType
    (stateAlias : TSyntax `ident) :
    CommandElabM (TSyntax `term) :=
  `(term| $stateAlias:ident → $stateAlias:ident)


-- private def mkExecuteAlt
--     (stateAlias : TSyntax `ident)
--     (stateIdent : TSyntax `ident)
--     (spec : InstrSpec) :
--     CommandElabM (TSyntax ``matchAlt) := do
--   let pat ← mkCtorPattern (mkIdent spec.instrName) (fieldsOfPieces spec.pieces)
--   let sem := spec.sem
--   let semTy ← mkMStateEndoType stateAlias
--   let semFn : TSyntax `term ← `(term| show $semTy:term from $sem:term)
--   let rhs : TSyntax `term ← `(term| $semFn:term $stateIdent:ident)
--   `(matchAltExpr| | $pat:term => $rhs:term)




-- private def mkExecuteCmd
--     (arch : ArchSpec) :
--     CommandElabM (TSyntax `command) := do
--   let typeName := arch.typeName
--   let execName := arch.execName
--   let alts ← arch.specs.mapM (mkExecuteAlt stateAlias stateIdent)
--   `(command|
--     def $(mkIdent execName) ($(mkIdent `_ms) : $(mkIdent `MState) $(mkIdent `Isntr))
--           ($(mkIdent `_instr) : $(mkIdent execName)) : $(mkIdent `MState) $(mkIdent `Isntr) :=
--       match $(mkIdent `_ms):ident with
--       $altLines:matchAlt*)

/-! Elaborators -/

def tres (stx : TSyntax `instr_set_spec) : CommandElabM (TSyntax `term) := do
  return ⟨stx⟩



  -- | `(term| mkInstrSet $archName:ident $typeName:ident $execName:ident $entries:instr_set_entry*) => do
  --     let specs ← liftM <| liftCommandElabM (entries.mapM mkCtorSpec)
  --     let arch : ArchSpec := {
  --       name     := archName.getId.eraseMacroScopes
  --       typeName := typeName.getId.eraseMacroScopes
  --       execName := execName.getId.eraseMacroScopes
  --       specs    := specs
  --     }

  --     pure (toExpr arch)
  -- | _ =>
  --     throwUnsupportedSyntax

-- def elabMkType : CommandElab := fun stx => do
--   match stx with
--   | `(command| mkType $archName:ident) => do
--       let arch ← resolveArchFromIdent archName
--       let indCmd ← mkInductiveCmd arch
--       logInfo s!"Created type {arch.typeName} for {arch.archName}"
--       elabCommand indCmd
--   | _ =>
--       throwUnsupportedSyntax

-- def elabMkExecution : CommandElab := fun stx => do
--   match stx with
--   | `(command| mkExecution $archName:ident) => do
--       let arch ← resolveArchFromIdent archName
--       let execCmd ← mkExecuteCmd arch
--       elabCommand execCmd
--   | _ =>
--       throwUnsupportedSyntax



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
  let ad : TSyntax `term ← `($(mkIdent arch.name))
  let indCmd ← mkInductiveCmd arch
  for instr in arch.specs do
    let syn ← mkSyntaxCmdForCtor instr
    elabCommand syn
  -- let exeCmd ← mkExecuteCmd arch
  logInfo s!"Created type {arch.typeName} for {arch.name}"
  -- logInfo s!"{arch.specs[0]!.hoareDesc}"
  elabCommand indCmd
  elabCommand (← mkGetInstrExprCmd arch)
  elabCommand (← mkTest)
  -- `mkTest` may emit extra elaborators/commands; keep it opt-in at call sites.
  -- elabCommand (← mkTest)
  -- elabCommand exeCmd
  -- let ad : TSyntax `term ← tres arch.specs[0]!.hoareDesc
  -- elabCommand (←`(#check $ad))


mkAll RV64 Instr execute
  LoadAddress:
    { syntax : la (a:register), (m:immediate),
      semantics: fun (ms) => (MState.addRegisterAt ms a m).incPc,
      specification: ⦃P ⟦x[a] <- m; pc++⟧⦄ pc ↦ ⟨{pc + 1} | {n : UInt64 | n ≠ pc + 1}⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄}
  LoadImmediate:
    { syntax : li (a:register), (m:immediate),
      semantics: fun ms => (MState.addRegisterAt ms a m).incPc,
      specification: true }
  Jump:
    { syntax : j (lbl:label),
      semantics: fun ms => (MState.jump ms lbl),
      specification: True }
  PANIC:
    { syntax : PANIC,
      semantics: fun ms => (MState.setTerminated ms true),
      specification: True }

#check ⟪j oaijdfsoi;⟫


elab "mriscx" t:mriscx_label* "end" : term => do
  return mkNatLit 0

#check mriscx
        first: li x0, 1
        end

#print getInstrExpr

def execute : MState Instr → Instr → MState Instr :=
fun ms instr =>
  if ms.terminated then ms
  else
    match instr with
    | Instr.LoadAddress a m => (fun ms => (ms.addRegisterAt a m).incPc) ms
    | Instr.LoadImmediate a m => (fun ms => (ms.addRegisterAt a m).incPc) ms
    | Instr.Jump lbl => (fun ms => ms.jump lbl) ms
    | Instr.PANIC => (fun ms => ms.setTerminated true) ms
#print Instr
-- #print execute

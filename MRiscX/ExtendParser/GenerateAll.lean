import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GenerateConcreteSyntax
import MRiscX.ExtendParser.GenerateElaborator
import MRiscX.ExtendParser.GenerateExecuteFunction
import MRiscX.ExtendParser.GenerateInstrToExpr
import MRiscX.ExtendParser.GenerateSpecDefinition
import Lean

open Lean
open Lean Elab Command
open MRiscX.ExtendParser.CommandElabShared

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

elab "mkAll " archName:ident typeName:ident execName:ident entries:instr_set_entry*: command => do
  let specs ← entries.mapM mkInstrSpecFromEntry
  let arch : ArchSpec := {
    name     := archName.getId.eraseMacroScopes
    typeName := typeName.getId.eraseMacroScopes
    execName := execName.getId.eraseMacroScopes
    specs    := specs
  }
  let ref := archName.raw
  let indCmd ← mkInductiveCmd ref arch
  -- concrete Syntax
  for instr in arch.specs do
    let syn ← mkSyntaxCmdForCtor instr
    withRef archName do
      elabCommand syn
  -- inductive instr type
  withRef archName do
    elabCommand indCmd
  -- Instr to Expr
  withRef archName do
    elabCommand (← mkGetInstrExprCmd ref arch)
  -- Elab for single Instr TODO automate
  withRef archName do
    elabCommand (← mkTest ref)
  -- Instr Specification
  for instr in arch.specs do
    for cmd in (← MRiscX.ExtendParser.GenerateSpecDefinition.mkSpecDefCmds ref arch instr "<mkAll>") do
      withRef archName do
        elabCommand cmd
  -- Execute command
  let exeCmd ← mkExecuteCmd ref arch
  withRef archName do
    elabCommand exeCmd
  -- elaboration
  liftIO <| activeArchRef.set (some arch)

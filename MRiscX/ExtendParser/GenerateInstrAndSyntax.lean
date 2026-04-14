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
  for instr in arch.specs do
    let syn ← mkSyntaxCmdForCtor instr
    withRef archName do
      elabCommand syn
  logInfo s!"Created type {arch.typeName} for {arch.name}"
  withRef archName do
    elabCommand indCmd
  withRef archName do
    elabCommand (← mkGetInstrExprCmd ref arch)
  withRef archName do
    elabCommand (← mkTest ref)
  for instr in arch.specs do
    withRef archName do
      elabCommand (← MRiscX.ExtendParser.GenerateSpecDefinition.mkSpecDefCmd ref arch instr "<mkAll>")
  let exeCmd ← mkExecuteCmd ref arch
  withRef archName do
    elabCommand exeCmd
  liftIO <| activeArchRef.set (some arch)

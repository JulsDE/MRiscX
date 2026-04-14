import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GenerateElaborator
import MRiscX.ExtendParser.GenerateSpecDefinition
import Lean

open Lean
open Lean Elab Command
open MRiscX.ExtendParser.CommandElabShared

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
        withRef archName do
          elabCommand (← MRiscX.ExtendParser.GenerateSpecDefinition.mkSpecDefCmd archName.raw arch spec "<mkSpecs>")
      let endCmd ← parseCommandStr archName.raw s!"end {nsName}" "<mkSpecs>"
      withRef archName do
        elabCommand endCmd
  | _ =>
      throwUnsupportedSyntax

@[command_elab mkSpecsCmd]
def elabMkSpecsImpl : CommandElab :=
  elabMkSpecs

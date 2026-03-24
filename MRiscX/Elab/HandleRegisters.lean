import MRiscX.Parser.AssemblySyntax
import Lean
open Lean Elab Meta Parser Expr

def parseRegister(r : TSyntax mriscx_registers) : TermElabM (TSyntax `term) :=
  `(0)

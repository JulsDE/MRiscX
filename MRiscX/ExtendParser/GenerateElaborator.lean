import MRiscX.AbstractSyntax.MState
import MRiscX.ExtendParser.AbstractSyntaxForGen
import MRiscX.ExtendParser.CommandElabShared
import MRiscX.ExtendParser.GeneralSyntax
import Lean

open Lean
open Lean Elab Command Term

syntax (name := mkElaboratorCmd)
  "mkElaborator " ident ident ident ppLine withPosition((colGe instr_set_entry)+) : command

initialize activeArchRef : IO.Ref (Option ArchSpec) ← IO.mkRef none

private def trimAsciiStr (s : String) : String :=
  (s.trimAscii).toString

private def sliceStr (s : String.Slice) : String :=
  s.toString

private def sanitizeInstrText (s : String) : String :=
  let s := trimAsciiStr s
  if s.endsWith ";" then
    trimAsciiStr (sliceStr (s.dropEnd 1))
  else
    s

private partial def skipSpaces (s : String) (i : Nat) : Nat :=
  if i < s.length then
    if (String.Pos.Raw.get s ⟨i⟩).isWhitespace then
      skipSpaces s (i + 1)
    else
      i
  else
    i

private def startsWithAt (s : String) (i : Nat) (tok : String) : Bool :=
  (s.drop i).startsWith tok

private partial def findTokenPos? (s : String) (tok : String) (start : Nat) : Option Nat :=
  let i := skipSpaces s start
  if i > s.length then
    none
  else if startsWithAt s i tok then
    some i
  else
    findTokenPos? s tok (i + 1)

private def nextLiteralTok? (pieces : Array Piece) (start : Nat) : Option String := Id.run do
  for i in [start:pieces.size] do
    match pieces[i]! with
    | .lit tok =>
        return some tok
    | .hole _ =>
        pure ()
  return none

private def splitHoleTexts (pieces : Array Piece) (raw : String) : Option (Array String) := Id.run do
  let s := sanitizeInstrText raw
  let mut pos := skipSpaces s 0
  let mut holes : Array String := #[]

  for i in [0:pieces.size] do
    match pieces[i]! with
    | .lit tok =>
        pos := skipSpaces s pos
        if startsWithAt s pos tok then
          pos := pos + tok.length
        else
          return none
    | .hole _ =>
        match nextLiteralTok? pieces (i + 1) with
        | some nextTok =>
            match findTokenPos? s nextTok pos with
            | some p =>
                holes := holes.push (trimAsciiStr (sliceStr ((s.drop pos).take (p - pos))))
                pos := p
            | none =>
                return none
        | none =>
            holes := holes.push (trimAsciiStr (sliceStr (s.drop pos)))
            pos := s.length

  pos := skipSpaces s pos
  if pos == s.length then
    some holes
  else
    none

private def parseTermStx (txt : String) : TermElabM (TSyntax `term) := do
  match Parser.runParserCategory (← getEnv) `term txt "<mkElaborator>" with
  | .ok stx =>
      pure ⟨stx⟩
  | .error err =>
      throwError s!"failed to parse term `{txt}`:\n{err}"

private def elabTermFromText (txt : String) (expectedType? : Option Expr := none) : TermElabM Expr := do
  let stx ← parseTermStx txt
  Lean.Elab.Term.elabTerm stx expectedType?

private def mkUInt64LitExpr (n : UInt64) : Expr :=
  mkApp3
    (mkConst ``OfNat.ofNat [levelZero])
    (mkConst ``UInt64)
    (mkRawNatLit n.toNat)
    (mkApp (mkConst ``UInt64.instOfNat) (mkRawNatLit n.toNat))

private def mkRegisterExpr (nr : Nat) (name : String) : Expr :=
  mkApp2
    (mkConst ``RegisterName.mk [])
    (mkApp (mkConst ``RegisterNr.ofNat []) (mkNatLit nr))
    (mkStrLit name)

private def mkRegisterExprFromUInt64Expr (v : Expr) (name : String) : Expr :=
  mkApp2
    (mkConst ``RegisterName.mk [])
    (mkApp (mkConst ``RegisterNr.ofUInt64 []) v)
    (mkStrLit name)

private def registerNrOfBare? (s : String) : Option Nat :=
  match s with
  | "x0" => some 0
  | "x1" => some 1
  | "x2" => some 2
  | "x3" => some 3
  | "x4" => some 4
  | "x5" => some 5
  | "x6" => some 6
  | "x7" => some 7
  | "x8" => some 8
  | "x9" => some 9
  | "x10" => some 10
  | "x11" => some 11
  | "x12" => some 12
  | "x13" => some 13
  | "x14" => some 14
  | "x15" => some 15
  | "x16" => some 16
  | "x17" => some 17
  | "x18" => some 18
  | "x19" => some 19
  | "x20" => some 20
  | "x21" => some 21
  | "x22" => some 22
  | "x23" => some 23
  | "x24" => some 24
  | "x25" => some 25
  | "x26" => some 26
  | "x27" => some 27
  | "x28" => some 28
  | "x29" => some 29
  | "x30" => some 30
  | "x31" => some 31
  | _ => none

private def registerNrOfAbi? (s : String) : Option Nat :=
  match s with
  | "zero" => some 0
  | "ra"   => some 1
  | "sp"   => some 2
  | "gp"   => some 3
  | "tp"   => some 4
  | "t0"   => some 5
  | "t1"   => some 6
  | "t2"   => some 7
  | "s0"   => some 8
  | "fp"   => some 8
  | "s1"   => some 9
  | "a0"   => some 10
  | "a1"   => some 11
  | "a2"   => some 12
  | "a3"   => some 13
  | "a4"   => some 14
  | "a5"   => some 15
  | "a6"   => some 16
  | "a7"   => some 17
  | "s2"   => some 18
  | "s3"   => some 19
  | "s4"   => some 20
  | "s5"   => some 21
  | "s6"   => some 22
  | "s7"   => some 23
  | "s8"   => some 24
  | "s9"   => some 25
  | "s10"  => some 26
  | "s11"  => some 27
  | "t3"   => some 28
  | "t4"   => some 29
  | "t5"   => some 30
  | "t6"   => some 31
  | _ => none

private def parseRegisterExpr (txt : String) : TermElabM Expr := do
  let s := trimAsciiStr txt
  match registerNrOfBare? s with
  | some nr =>
      pure (mkRegisterExpr nr s)
  | none =>
      match registerNrOfAbi? s with
      | some nr =>
          pure (mkRegisterExpr nr s)
      | none =>
          if s.startsWith "x" then
            let rest := trimAsciiStr (sliceStr (s.drop 1))
            if rest.isEmpty then
              throwError s!"invalid register `{txt}`"
            else
              match rest.toNat? with
              | some n =>
                  pure (mkRegisterExprFromUInt64Expr (mkUInt64LitExpr n.toUInt64) s)
              | none =>
                  let nExpr ← elabTermFromText rest (some (mkConst ``UInt64 []))
                  pure (mkRegisterExprFromUInt64Expr nExpr s)
          else
            throwError s!"invalid register `{txt}`"

private def holeExprFromText (hole : Hole) (txt : String) : TermElabM Expr := do
  let p := hole.parser
  if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "register" then
    parseRegisterExpr txt
  else if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "label" then
    pure (mkStrLit (trimAsciiStr txt))
  else if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "immediate" then
    elabTermFromText txt (some (mkConst ``UInt64 []))
  else
    let tyExpr ← elabTermFromText hole.ty none
    elabTermFromText txt (some tyExpr)

private def defaultHoleExpr (hole : Hole) : TermElabM Expr := do
  let p := hole.parser
  if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "register" then
    pure (mkRegisterExpr 0 "zero")
  else if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "label" then
    pure (mkStrLit "")
  else if MRiscX.ExtendParser.CommandElabShared.parserTextEq p "immediate" then
    pure (mkUInt64LitExpr 0)
  else
    let tyExpr ← elabTermFromText hole.ty none
    elabTermFromText s!"(default : {hole.ty})" (some tyExpr)

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

private def mkInstrExprForCtor (arch : ArchSpec) (spec : InstrSpec) (holeTexts : Array String) : TermElabM Expr := do
  let mut holeIdx := 0
  let mut args : Array Expr := #[]
  for piece in spec.pieces do
    match piece with
    | .lit _ =>
        pure ()
    | .hole h =>
        if hHole : holeIdx < holeTexts.size then
          args := args.push (← holeExprFromText h holeTexts[holeIdx])
          holeIdx := holeIdx + 1
        else
          throwError s!"internal error: missing hole text in `{spec.instrName}`"
  let ctorConst := qualifyCtorName arch.typeName spec.instrName
  pure (mkAppN (.const ctorConst []) args)

private def mkDefaultInstrExpr (arch : ArchSpec) : TermElabM Expr := do
  let some first := arch.specs[0]?
    | throwError "architecture has no constructors; cannot build default instruction map entry"
  let mut args : Array Expr := #[]
  for piece in first.pieces do
    match piece with
    | .lit _ =>
        pure ()
    | .hole h =>
        args := args.push (← defaultHoleExpr h)
  let ctorConst := qualifyCtorName arch.typeName first.instrName
  pure (mkAppN (.const ctorConst []) args)

private def mkInstrExpr (arch : ArchSpec) (instr : TSyntax `mriscx_Instr) : TermElabM Expr := do
  let txt := instr.raw.reprint.getD (toString instr.raw)
  for spec in arch.specs do
    match splitHoleTexts spec.pieces txt with
    | some holeTexts =>
        return (← mkInstrExprForCtor arch spec holeTexts)
    | none =>
        pure ()
  throwError s!"unknown instruction syntax `{sanitizeInstrText txt}` for architecture `{arch.name}`"

private def getLabelInstrs (arch : ArchSpec) (lbl : TSyntax `mriscx_label) : TermElabM (String × Array Expr) := do
  match lbl with
  | `(mriscx_label| $name:ident : $seq:mriscx_Instr*) => do
      let mut instrs : Array Expr := #[]
      for i in seq do
        instrs := instrs.push (← mkInstrExpr arch i)
      pure (name.getId.eraseMacroScopes.toString, instrs)
  | _ =>
      throwError "expected label block"

private def mkCodeExprFromSyntax (arch : ArchSpec) (syn : TSyntax `mriscx_syntax) : TermElabM Expr := do
  match syn with
  | `(mriscx_syntax| mriscx
      $lbls:mriscx_label*
      end) => do
      let mut labeledInstrs : Array (String × Array Expr) := #[]
      for l in lbls do
        labeledInstrs := labeledInstrs.push (← getLabelInstrs arch l)

      let instrTy := Lean.mkConst (arch.typeName.eraseMacroScopes) []
      let defaultInstr ← mkDefaultInstrExpr arch
      let mut instrMap := mkAppN (Lean.mkConst ``TMap.empty []) #[Lean.mkConst ``UInt64 [], instrTy, defaultInstr]
      let mut labelMap := mkAppN (Lean.mkConst ``PMap.empty []) #[Lean.mkConst ``String [], Lean.mkConst ``UInt64 []]

      let mut pc : UInt64 := 0
      for (lbl, instrs) in labeledInstrs do
        labelMap ← Lean.Meta.mkAppM ``PMap.put #[mkStrLit lbl, mkUInt64LitExpr pc, labelMap]
        for iExpr in instrs do
          instrMap ← Lean.Meta.mkAppM ``TMap.put #[mkUInt64LitExpr pc, iExpr, instrMap]
          pc := pc + 1

      pure (mkAppN (Lean.mkConst ``Code.mk []) #[instrTy, labelMap, instrMap])
  | _ =>
      throwError "expected `mriscx ... end` syntax"

-- def elabMkElaborator : CommandElab := fun stx => do
--   match stx with
--   | `(command| mkElaborator $archName:ident $typeName:ident $execName:ident $entries:instr_set_entry*) => do
--       let specs ← entries.mapM MRiscX.ExtendParser.CommandElabShared.mkInstrSpecFromEntry
--       let arch : ArchSpec := {
--         name := archName.getId.eraseMacroScopes
--         typeName := typeName.getId.eraseMacroScopes
--         execName := execName.getId.eraseMacroScopes
--         specs := specs
--       }
--       liftIO <| activeArchRef.set (some arch)
--   | _ =>
--       throwUnsupportedSyntax

-- @[command_elab mkElaboratorCmd]
-- def elabMkElaboratorImpl : CommandElab :=
--   elabMkElaborator

@[term_elab mriscxTerm]
def elabMriscxGenerated : TermElab := fun stx expectedType? => do
  let some arch ← liftM (m := TermElabM) <| activeArchRef.get
    | throwError "no active architecture elaborator; run `mkAll ...` first"
  match stx with
  | `(term| $syn:mriscx_syntax) =>
      let e ← mkCodeExprFromSyntax arch syn
      match expectedType? with
      | some t =>
          Lean.Elab.Term.ensureHasType t e
      | none =>
          pure e
  | _ =>
      throwUnsupportedSyntax

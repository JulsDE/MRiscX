import Lean
import MRiscX.AbstractSyntax.MState

open Lean
open Lean Elab Command
open Lean Meta

/-!
Shared decoded view used by `mkType`, `mkExecution`, and `mkSyntax`.
-/


structure Hole where
  name   : Name
  ty     : String
  parser : String
deriving Repr, Inhabited, ToExpr

inductive Piece where
  | lit  (token : String)
  | hole (value : Hole)
deriving Repr, Inhabited, ToExpr

structure InstrSpec where
  ref      : String
  instrName : Name
  pieces   : Array Piece
  sem      : String
  hoareDesc: TSyntax `instr_set_spec
deriving Repr, Inhabited --, ToExpr

structure ArchSpec where
  name     : Name
  typeName : Name
  execName : Name
  specs    : Array InstrSpec
deriving Repr, Inhabited --, ToExpr


def fieldsOfPieces (pieces : Array Piece) : (Array Hole) :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push h

private def trimAsciiStr (s : String) : String :=
  (s.trimAscii).toString


/-! Expr decoding (safe; no `unsafe` / no `evalExpr`). -/

private def n (s : String) : Name :=
  s.splitOn "." |>.foldl (init := .anonymous) Name.str

private def nameMatches (fn : Name) (expected : String) : Bool :=
  let full := toString fn
  full == expected || full.endsWith s!".{expected}"

-- def decodeError {α} (expected : String) (e : Expr) : CommandElabM α :=
--   throwError s!"failed to decode {expected} from expression:\n{e}"

-- def decodeStringExpr (e : Expr) : CommandElabM String := do
--   match e.consumeMData with
--   | .lit (.strVal s) =>
--       pure s
--   | other =>
--       decodeError "String" other

-- def decodeNatExpr (e : Expr) : CommandElabM Nat := do
--   match e.consumeMData with
--   | .lit (.natVal v) =>
--       pure v
--   | other =>
--       decodeError "Nat" other

-- partial def decodeNameExpr (e : Expr) : CommandElabM Name := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "Lean.Name.anonymous" then
--     pure .anonymous
--   else if fn == n "Lean.Name.str" then
--     if args.size = 2 then
--       pure <| .str (← decodeNameExpr args[0]!) (← decodeStringExpr args[1]!)
--     else
--       decodeError "Lean.Name.str" e
--   else if fn == n "Lean.Name.num" then
--     if args.size = 2 then
--       pure <| .num (← decodeNameExpr args[0]!) (← decodeNatExpr args[1]!)
--     else
--       decodeError "Lean.Name.num" e
--   else if fn == n "Lean.Name.mkStr1" then
--     if args.size = 1 then
--       pure <| .str .anonymous (← decodeStringExpr args[0]!)
--     else
--       decodeError "Lean.Name.mkStr1" e
--   else if fn == n "Lean.Name.mkStr2" then
--     if args.size = 2 then
--       pure <| .str (.str .anonymous (← decodeStringExpr args[0]!)) (← decodeStringExpr args[1]!)
--     else
--       decodeError "Lean.Name.mkStr2" e
--   else if fn == n "Lean.Name.mkStr3" then
--     if args.size = 3 then
--       pure <| .str (.str (.str .anonymous (← decodeStringExpr args[0]!)) (← decodeStringExpr args[1]!))
--                     (← decodeStringExpr args[2]!)
--     else
--       decodeError "Lean.Name.mkStr3" e
--   else if fn == n "Lean.Name.mkStr4" then
--     if args.size = 4 then
--       pure <| .str
--         (.str
--           (.str (.str .anonymous (← decodeStringExpr args[0]!)) (← decodeStringExpr args[1]!))
--           (← decodeStringExpr args[2]!))
--         (← decodeStringExpr args[3]!)
--     else
--       decodeError "Lean.Name.mkStr4" e
--   else
--     decodeError "Name" e

-- partial def decodeListExpr
--     (decodeElem : Expr → CommandElabM α)
--     (e : Expr) :
--     CommandElabM (List α) := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "List.nil" then
--     pure []
--   else if fn == n "List.cons" then
--     if args.size = 3 then
--       pure ((← decodeElem args[1]!) :: (← decodeListExpr decodeElem args[2]!))
--     else
--       decodeError "List.cons" e
--   else
--     decodeError "List" e

-- partial def decodeArrayExpr
--     (decodeElem : Expr → CommandElabM α)
--     (e : Expr) :
--     CommandElabM (Array α) := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "List.toArray" then
--     if args.size = 2 then
--       pure (← decodeListExpr decodeElem args[1]!).toArray
--     else
--       decodeError "List.toArray" e
--   else if fn == n "Array.empty" then
--     pure #[]
--   else if fn == n "Array.push" then
--     if args.size = 3 then
--       let arr ← decodeArrayExpr decodeElem args[1]!
--       let elem ← decodeElem args[2]!
--       pure (arr.push elem)
--     else
--       decodeError "Array.push" e
--   else
--     decodeError "Array" e

-- private def decodePosRawExpr (e : Expr) : CommandElabM String.Pos.Raw := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "String.Pos.Raw.mk" then
--     if args.size = 1 then
--       pure ⟨← decodeNatExpr args[0]!⟩
--     else
--       decodeError "String.Pos.Raw.mk" e
--   else
--     decodeError "String.Pos.Raw" e

-- private def decodeSubstringRawExpr (e : Expr) : CommandElabM Substring.Raw := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "Substring.Raw.mk" then
--     if args.size = 3 then
--       pure <| Substring.Raw.mk
--         (← decodeStringExpr args[0]!)
--         (← decodePosRawExpr args[1]!)
--         (← decodePosRawExpr args[2]!)
--     else
--       decodeError "Substring.Raw.mk" e
--   else
--     decodeError "Substring.Raw" e

-- private partial def decodeSyntaxExpr (e : Expr) : CommandElabM Syntax := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "Syntax.missing" then
--     pure Syntax.missing
--   else if fn == n "Syntax.node" then
--     if args.size = 3 then
--       pure <| Syntax.node
--         SourceInfo.none
--         (← decodeNameExpr args[1]!)
--         (← decodeArrayExpr decodeSyntaxExpr args[2]!)
--     else
--       decodeError "Syntax.node" e
--   else if fn == n "Syntax.atom" then
--     if args.size = 2 then
--       pure <| Syntax.atom SourceInfo.none (← decodeStringExpr args[1]!)
--     else
--       decodeError "Syntax.atom" e
--   else if fn == n "Syntax.ident" then
--     if args.size = 4 then
--       pure <| Syntax.ident
--         SourceInfo.none
--         (← decodeSubstringRawExpr args[1]!)
--         (← decodeNameExpr args[2]!)
--         []
--     else
--       decodeError "Syntax.ident" e
--   else
--     decodeError "Syntax" e

-- private def decodeTSyntaxRawExpr (e : Expr) : CommandElabM Syntax := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if fn == n "Lean.TSyntax.mk" then
--     if args.size = 2 then
--       decodeSyntaxExpr args[1]!
--     else
--       decodeError "Lean.TSyntax.mk" e
--   else
--     decodeError "TSyntax" e

-- private def decodeTextFromTSyntaxExpr (e : Expr) : CommandElabM String := do
--   let stx ← decodeTSyntaxRawExpr e
--   pure <| trimAsciiStr (stx.reprint.getD (toString stx))

-- private def isNameCtorExpr (fn : Name) : Bool :=
--   nameMatches fn "Lean.Name.anonymous" ||
--   nameMatches fn "Lean.Name.str" ||
--   nameMatches fn "Lean.Name.num" ||
--   nameMatches fn "Lean.Name.mkStr1" ||
--   nameMatches fn "Lean.Name.mkStr2" ||
--   nameMatches fn "Lean.Name.mkStr3" ||
--   nameMatches fn "Lean.Name.mkStr4"

-- private def decodeNameFromSyntax (stx : Syntax) : CommandElabM Name := do
--   match stx with
--   | .ident _ _ val _ =>
--       pure (val.eraseMacroScopes)
--   | .atom _ tok =>
--       pure (Name.mkSimple (trimAsciiStr tok))
--   | other =>
--       let txt := trimAsciiStr (other.reprint.getD (toString other))
--       if txt.isEmpty then
--         throwError s!"failed to decode name-like syntax from:\n{other}"
--       else
--         pure (Name.mkSimple txt)

-- private def decodeNameLikeExpr (e : Expr) : CommandElabM Name := do
--   let e := e.consumeMData
--   match e with
--   | .lit (.strVal s) =>
--       pure (Name.mkSimple (trimAsciiStr s))
--   | _ =>
--       let (fn, _) := e.getAppFnArgs
--       if isNameCtorExpr fn then
--         decodeNameExpr e
--       else if fn == n "Lean.TSyntax.mk" then
--         decodeNameFromSyntax (← decodeTSyntaxRawExpr e)
--       else
--         decodeError "Name-like value" e

-- private def decodeTypeTextExpr (e : Expr) : CommandElabM String := do
--   let e := e.consumeMData
--   match e with
--   | .lit (.strVal s) =>
--       pure s
--   | _ =>
--       let (fn, _) := e.getAppFnArgs
--       if fn == n "Lean.TSyntax.mk" then
--         decodeTextFromTSyntaxExpr e
--       else if isNameCtorExpr fn then
--         pure (toString (← decodeNameExpr e))
--       else
--         decodeError "hole type" e

-- private def decodeParserExpr (e : Expr) : CommandElabM Name := do
--   let e := e.consumeMData
--   match e with
--   | .lit (.strVal s) =>
--       pure (Name.mkSimple (trimAsciiStr s))
--   | _ =>
--       let (fn, _) := e.getAppFnArgs
--       if isNameCtorExpr fn then
--         decodeNameExpr e
--       else if fn == n "Lean.TSyntax.mk" then
--         let txt ← decodeTextFromTSyntaxExpr e
--         pure (Name.mkSimple txt)
--       else
--         decodeError "hole parser" e

-- private def decodeSemTextExpr (e : Expr) : CommandElabM String := do
--   let e := e.consumeMData
--   match e with
--   | .lit (.strVal s) =>
--       pure s
--   | _ =>
--       let (fn, _) := e.getAppFnArgs
--       if fn == n "Lean.TSyntax.mk" then
--         decodeTextFromTSyntaxExpr e
--       else
--         decodeError "constructor semantics" e

-- def decodeHoleExpr (e : Expr#) : CommandElabM Hole := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if nameMatches fn "Hole.mk" then
--     if args.size = 3 then
--       pure {
--         name   := ← decodeNameLikeExpr args[0]!
--         ty := ← decodeTypeTextExpr args[1]!
--         parser := ← decodeParserExpr args[2]!
--       }
--     else
--       decodeError "Hole.mk" e
--   else
--     decodeError "Hole" e

-- def decodePieceExpr (e : Expr) : CommandElabM Piece := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if nameMatches fn "Piece.lit" then
--     if args.size = 1 then
--       pure <| .lit (← decodeStringExpr args[0]!)
--     else
--       decodeError "Piece.lit" e
--   else if nameMatches fn "Piece.hole" then
--     if args.size = 1 then
--       pure <| .hole (← decodeHoleExpr args[0]!)
--     else
--       decodeError "Piece.hole" e
--   else
--     decodeError "Piece" e

-- def decodeCtorExpr (e : Expr) : CommandElabM InstrSpec := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if nameMatches fn "CtorSpec.mk" then
--     if args.size = 5 then
--       pure {
--         ctorName := ← decodeNameLikeExpr args[1]!
--         pieces   := ← decodeArrayExpr decodePieceExpr args[2]!
--         semText  := ← decodeSemTextExpr args[3]!
--         specText := ← decodeSemTextExpr args[4]!
--       }
--     else if args.size = 4 then
--       pure {
--         ctorName := ← decodeNameLikeExpr args[1]!
--         pieces   := ← decodeArrayExpr decodePieceExpr args[2]!
--         semText  := ← decodeSemTextExpr args[3]!
--         specText := "True"
--       }
--     else
--       decodeError "CtorSpec.mk" e
--   else
--     decodeError "CtorSpec" e

-- def decodeArchExpr (e : Expr) : CommandElabM ArchSpec := do
--   let e := e.consumeMData
--   let (fn, args) := e.getAppFnArgs
--   if nameMatches fn "ArchSpec.mk" then
--     if args.size = 4 then
--       let archName ←
--         try
--           decodeNameLikeExpr args[0]!
--         catch _ =>
--           pure Name.anonymous
--       pure {
--         archName := archName
--         typeName := ← decodeNameLikeExpr args[1]!
--         execName := ← decodeNameLikeExpr args[2]!
--         ctors    := ← decodeArrayExpr decodeCtorExpr args[3]!
--       }
--     else
--       decodeError "ArchSpec.mk" e
--   else
--     decodeError "ArchSpec" e

-- def resolveArchFromIdent (archName : TSyntax `ident) : CommandElabM ArchSpec := do
--   let target := archName.getId.eraseMacroScopes
--   let info ← getConstInfo target
--   let some value := info.value? (allowOpaque := true)
--     | throwErrorAt archName s!"`{target}` is not reducible to an `ArchSpec` value"
--   let whnfValue ← liftTermElabM <| Meta.withTransparency .all <| Meta.whnf value
--   decodeArchExpr whnfValue

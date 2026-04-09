import MRiscX.AbstractSyntax.MState
-- import MRiscX.ExtendParser.idea

import Lean

open Lean Meta
open Lean Elab Command
open Lean.Parser.Command
open Lean.Parser.Term

/-!
  Platzhalter in einem `syntax:`-Block, z. B.

    (dst : Nat, mriscx_num_or_ident)

  Der zweite Slot ist bewusst `stx` statt nur `ident`.
-/
declare_syntax_cat register
declare_syntax_cat immediate
declare_syntax_cat label
declare_syntax_cat num_or_ident

syntax num : num_or_ident

syntax ident : num_or_ident

syntax &"x" num_or_ident : register
syntax "x0" : register

syntax num_or_ident : immediate

syntax ident : label


declare_syntax_cat instr_set_hole

syntax register : instr_set_hole
syntax immediate : instr_set_hole
syntax label : instr_set_hole

-- syntax "(" ident ":" term "," stx ")" : instr_set_hole

syntax "(" ident ":" stx ")" : instr_set_hole

-- la (r:register), (i:immediate)
-- j (l:label)
/-!
  Bausteine der konkreten Syntax.

  Die Liste ist absichtlich überschaubar gehalten und deckt dein Beispiel ab.
  Falls du später mehr Literal-Tokens brauchst, kannst du hier einfach weitere
  `syntax ... : instr_set_piece`-Zeilen ergänzen.
-/
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

/--
Eine Folge von `instr_set_piece`, die genau bis vor `, semantics:` reicht.
-/
declare_syntax_cat instr_set_sig
syntax ((!(("," "semantics" ":"))) instr_set_piece)+ : instr_set_sig

/--
Ein Eintrag der Form

  LoadAddress:
    { syntax: ...,
      semantics: ... }
-/
declare_syntax_cat instr_set_entry
syntax ident ":" "{" "syntax" ":" instr_set_sig "," "semantics" ":" term "}" : instr_set_entry

syntax (name := makeInstrSet)
  "make_InstrSet " ident ident ident ppLine withPosition((colGe instr_set_entry)+) : command

syntax (name := mkInstrTypeCmd)
  "mkInstrType " term : command

syntax (name := mkInstrSetTerm)
  "mkInstrSet " instr_set_entry : term

syntax (name := mkInstrSetArchTerm)
  "mkInstrSet " ident ident ident ppLine withPosition((colGe instr_set_entry)+) : term



/-! ## Interne Repräsentation -/

deriving instance ToExpr for SyntaxNodeKinds

structure Hole where
  name   : Name
  ty     : Term
  parser : Name
deriving Repr

inductive Piece where
  | lit  (tok : String)
  | hole (h : Hole)
deriving Repr

structure CtorSpec where
  ref      : Name
  ctorName : Name
  pieces   : Array Piece
  sem      : Term
deriving Repr

structure ArchSpec where
  name     : Name
  typeName : Name
  execName : Name
  specs    : Array CtorSpec
deriving Repr

instance : ToString Hole where
  toString h :=
    s!"Hole(name := {reprStr h.name}, ty := {reprStr h.ty}, parser := {reprStr h.parser})"

instance : ToString Piece where
  toString
    | .lit tok => s!"Piece.lit({reprStr tok})"
    | .hole h  => s!"Piece.hole({toString h})"

instance : ToString CtorSpec where
  toString c :=
    s!"CtorSpec(ref := {reprStr c.ref}, \n\nctorName := {reprStr c.ctorName},\n\npieces := {reprStr c.pieces},\n\nsem := {reprStr c.sem})"


/-! ## Kleine Hilfsfunktionen -/

private def quoteStringLit (s : String) : String :=
  let escaped :=
    s.toList.foldl (init := "") fun acc c =>
      acc ++
        match c with
        | '\"' => "\\\""
        | '\\' => "\\\\"
        | '\n' => "\\n"
        | '\t' => "\\t"
        | '\r' => "\\r"
        | c    => String.singleton c
  "\"" ++ escaped ++ "\""

private def parseAs (cat : Name) (input : String) (ref : Name) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) cat input "<make_InstrAS>" with
  | .ok stx =>
      pure stx
  | .error err =>
      throwError s!"Fehler beim Parsen von `{input}` als `{cat}` in `{ref}`:\n{err}"

private def parseStx (ref : Name) (input : String) : CommandElabM (TSyntax `stx) := do
  pure ⟨← parseAs `stx input ref⟩


#check Array

/--
Liest aus einem sehr kleinen Syntaxbaum den ersten Token-Text heraus.
Für unsere `instr_set_piece`-Knoten ist genau das der gewünschte Literaltext.
-/
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

private def isIdentLikeTok (tok : String) : Bool :=
  let rec loop : List Char → Bool
    | []      => true
    | c :: cs => (c.isAlphanum || c == '_' || c == '\'') && loop cs
  tok.length > 0 && loop tok.toList

private def isPunctuationTok (tok : String) : Bool :=
  tok == ","  || tok == ";"  || tok == ":"  || tok == "." ||
  tok == "+"  || tok == "-"  || tok == "*"  || tok == "/" ||
  tok == "="  || tok == "<"  || tok == ">"  ||
  tok == "<=" || tok == ">="

/--
Heuristik für Pretty-Printing-Hinweise in den generierten `syntax`-Atoms.
Parserisch ist `"la"` äquivalent zu `"la "`, die Leerzeichen steuern hier nur
das Pretty Printing.
-/
private def decorateAtomText (tok : String) (isFirst : Bool) (hasNext : Bool) : String :=
  if (tok == "," || tok == ";" || tok == ":") && hasNext then
    tok ++ " "
  else if isIdentLikeTok tok && isFirst && hasNext then
    tok ++ " "
  else
    tok

/--
Heuristik dafür, wann `&"..."` statt `"..."` verwendet wird.

- erste, längere Mnemonics wie `la`, `mv`, `panic` werden als normale Atome
  ausgegeben;
- einbuchstabige Tokens wie `x` oder `j` sowie Satzzeichen werden nicht reserviert.
-/
private def useNonReservedAtom (tok : String) (isFirst : Bool) : Bool :=
  if isIdentLikeTok tok then
    !(isFirst && tok.length > 1)
  else
    isPunctuationTok tok

private def mkLiteralStx
    (ref : Name)
    (tok : String)
    (isFirst : Bool)
    (hasNext : Bool) :
    CommandElabM (TSyntax `stx) := do
  let txt := decorateAtomText tok isFirst hasNext
  let txtQ := quoteStringLit txt
  if useNonReservedAtom tok isFirst then
    parseStx ref s!"&{txtQ}"
  else
    parseStx ref txtQ

private def fieldsOfPieces (pieces : Array Piece) : Array (Name × Term) :=
  pieces.foldl (init := #[]) fun acc piece =>
    match piece with
    | .lit _   => acc
    | .hole h  => acc.push (h.name, h.ty)

private def ensureNoDuplicateFieldNames
    (ctorName : Name)
    (fields : Array (Name × Term)) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for (name, _) in fields do
    let n := name.eraseMacroScopes
    if seen.contains n then
      throwError s!"doppelter Platzhaltername `{n}` im Konstruktor `{ctorName}`"
    seen := seen.push n


/-! ## Einträge aus der DSL lesen -/

private def elabPiece (piece : TSyntax `instr_set_piece) : CommandElabM Piece := do
  match piece with
  | `(instr_set_piece| $h:instr_set_hole) =>
      match h with
      | `(instr_set_hole| ($name:ident : $parser:stx)) =>
          let holeName := name.getId
          match parser with
          | `(stx | register) =>
            let ty: TSyntax `term ← `(term | RegisterName)
            pure <| .hole { name := holeName, ty, parser := `register }
          | `(stx | label) =>
            let ty: TSyntax `term ← `(term | String)
            pure <| .hole { name := holeName, ty, parser := `label }
          | `(stx | immediate) =>
            let ty: TSyntax `term ← `(term | UInt64)
            pure <| .hole { name := holeName, ty, parser := `immediate }
          | _ =>
            throwError s!"No valid syntax type: {parser.raw.getArgs[0]!}`. Must be `register`" ++
                          "`immediate` or `label`!"
      | _ =>
          throwErrorAt h "interner Fehler: ungültiger Platzhalter"
  | _ =>
      match leafTokenText? piece.raw with
      | some tok =>
          pure <| .lit tok
      | none =>
          throwErrorAt piece "interner Fehler: Tokentext konnte nicht rekonstruiert werden"

private def extractPieces
    (sig : TSyntax `instr_set_sig) :
    CommandElabM (Array Piece) := do
  match sig with
  | `(instr_set_sig| $[$pieces:instr_set_piece]*) =>
      pieces.mapM elabPiece
  | _ =>
      throwErrorAt sig "interner Fehler: ungültige Syntaxbeschreibung"

private def mkCtorSpec
    (entry : TSyntax `instr_set_entry) :
    CommandElabM CtorSpec := do
  match entry with
  | `(instr_set_entry| $ctorName:ident : { syntax : $sig:instr_set_sig, semantics : $sem:term }) => do
      let pieces ← extractPieces sig
      let fields := fieldsOfPieces pieces
      let ctorName := ctorName.getId
      ensureNoDuplicateFieldNames ctorName fields
      pure {
        ref      := ctorName
        ctorName := ctorName
        pieces   := pieces
        sem      := sem
      }
  | _ =>
      throwErrorAt entry "interner Fehler: ungültiger Instruktions-Eintrag"


/-! ## `CtorSpec` als Term -/

private def posRawToExpr (p : String.Pos.Raw) : Expr :=
  mkApp (.const ``String.Pos.Raw.mk []) (toExpr p.byteIdx)

private def substringRawToExpr (s : Substring.Raw) : Expr :=
  mkApp3 (.const ``Substring.Raw.mk [])
    (toExpr s.str)
    (posRawToExpr s.startPos)
    (posRawToExpr s.stopPos)

private def sourceInfoToExpr : SourceInfo → Expr
  | .none =>
      .const ``SourceInfo.none []
  | .original leading pos trailing endPos =>
      mkApp4 (.const ``SourceInfo.original [])
        (substringRawToExpr leading)
        (posRawToExpr pos)
        (substringRawToExpr trailing)
        (posRawToExpr endPos)
  | .synthetic pos endPos canonical =>
      mkApp3 (.const ``SourceInfo.synthetic [])
        (posRawToExpr pos)
        (posRawToExpr endPos)
        (toExpr canonical)

private def mkArrayExpr (elemTy : Expr) (elems : Array Expr) : Expr :=
  elems.foldl
    (init := mkApp (.const ``Array.empty [levelZero]) elemTy)
    (fun arr elem => mkApp3 (.const ``Array.push [levelZero]) elemTy arr elem)

private partial def syntaxToExpr : Syntax → Expr
  | .missing =>
      .const ``Syntax.missing []
  | .node info kind args =>
      mkApp3 (.const ``Syntax.node [])
        (sourceInfoToExpr info)
        (toExpr kind)
        (mkArrayExpr (.const ``Syntax []) (args.map syntaxToExpr))
  | .atom info val =>
      mkApp2 (.const ``Syntax.atom [])
        (sourceInfoToExpr info)
        (toExpr val)
  | .ident info rawVal val preresolved =>
      mkApp4 (.const ``Syntax.ident [])
        (sourceInfoToExpr info)
        (substringRawToExpr rawVal)
        (toExpr val)
        (toExpr preresolved)

private def tSyntaxToExpr (ks : SyntaxNodeKinds) (stx : TSyntax ks) : Expr :=
  mkApp2 (.const ``TSyntax.mk [])
    (toExpr ks)
    (syntaxToExpr stx.raw)

private def holeToExpr (h : Hole) : Expr :=
  mkApp3 (.const ``Hole.mk [])
    (toExpr h.name)
    (tSyntaxToExpr `term h.ty)
    (toExpr h.parser)

private def pieceToExpr : Piece → Expr
  | .lit tok =>
      mkApp (.const ``Piece.lit []) (toExpr tok)
  | .hole h =>
      mkApp (.const ``Piece.hole []) (holeToExpr h)

private def ctorSpecToExpr (spec : CtorSpec) : Expr :=
  mkApp4 (.const ``CtorSpec.mk [])
    (toExpr spec.ref)
    (toExpr spec.ctorName)
    (mkArrayExpr (.const ``Piece []) (spec.pieces.map pieceToExpr))
    (tSyntaxToExpr `term spec.sem)

private def archSpecToExpr
    (name : Name)
    (typeName : Name)
    (execName : Name)
    (specs : Array CtorSpec) : Expr :=
  mkApp4 (.const ``ArchSpec.mk [])
    (toExpr name)
    (toExpr typeName)
    (toExpr execName)
    (mkArrayExpr (.const ``CtorSpec []) (specs.map ctorSpecToExpr))

def elabMkInstrSetTerm : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let _ := expectedType?
  match stx with
  | `(term| mkInstrSet $entry:instr_set_entry) =>
      let spec ← liftM <| liftCommandElabM (mkCtorSpec entry)
      pure (ctorSpecToExpr spec)
  | `(term| mkInstrSet $name:ident $typeName:ident $execName:ident $entries:instr_set_entry*) => do
      let specs ← liftM <| liftCommandElabM (entries.mapM mkCtorSpec)
      pure (archSpecToExpr name.getId typeName.getId execName.getId specs)
  | _ =>
      throwUnsupportedSyntax


/-! ## Induktiver Datentyp -/

private def mkArrowType
    (argTys : List (TSyntax `term))
    (resultTy : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  match argTys with
  | [] =>
      pure resultTy
  | ty :: tys =>
      let rest ← mkArrowType tys resultTy
      `(term| ($ty:term) → $rest:term)

private def mkCtorType
    (typeName : TSyntax `ident)
    (fields : Array (Name × Term)) :
    CommandElabM (TSyntax `term) := do
  let resultTy : TSyntax `term ← `(term| $typeName:ident)
  let argTys : List (TSyntax `term) := fields.toList.map (fun f => f.2)
  mkArrowType argTys resultTy

private def mkCtorDecl
    (typeName : TSyntax `ident)
    (spec : CtorSpec) :
    CommandElabM (TSyntax ``ctor) := do
  let fields := fieldsOfPieces spec.pieces
  let ctorTy ← mkCtorType typeName fields
  let ctorName := mkIdent spec.ctorName
  `(ctor| | $ctorName:ident : $ctorTy:term)

private def mkInductiveCmd
    (typeName : TSyntax `ident)
    (specs : Array CtorSpec) :
    CommandElabM (TSyntax `command) := do
  let ctorDecls ← specs.mapM (mkCtorDecl typeName)
  `(command|
    inductive $typeName:ident : Type where
      $ctorDecls:ctor*
    deriving Repr, BEq, Inhabited)


/-! ## Generierte `syntax`-Deklarationen -/

private def mkTargetSyntaxCatName (typeName : TSyntax `ident) : TSyntax `ident :=
  let n := typeName.getId.eraseMacroScopes
  let catName :=
    match n with
    | .str p s => Name.str p ("mriscx_" ++ s)
    | _        => Name.str .anonymous ("mriscx_" ++ toString n)
  mkIdentFrom typeName catName

deriving instance Inhabited for Piece

private def mkSyntaxItems (spec : CtorSpec) : CommandElabM (Array (TSyntax `stx)) := do
  let mut items : Array (TSyntax `stx) := #[]
  let n := spec.pieces.size
  for i in [0:n] do
    let hasNext := i + 1 < n
    match spec.pieces[i]! with
    | .hole h =>
        items := items.push (← parseStx spec.ref (toString h.parser))
    | .lit tok =>
        items := items.push (← mkLiteralStx spec.ref tok (i == 0) hasNext)
  pure items

private def mkSyntaxCmd
    (typeName : TSyntax `ident)
    (spec : CtorSpec) :
    CommandElabM (TSyntax `command) := do
  let targetCat := mkTargetSyntaxCatName typeName
  let items ← mkSyntaxItems spec
  let terminator : TSyntax `stx ← `(stx| withPosition(Lean.Parser.semicolonOrLinebreak ppDedent(ppLine)))
  let items := items.push terminator
  `(command| syntax $[$items:stx]* : $targetCat:ident)


/-! ## Generierte Semantikfunktion -/
private def mkPatArg
    (name : Name)
    (ty : Term) :
    CommandElabM (TSyntax `term) := do
  let name := mkIdent name
  `(term| ($name:ident : $ty:term))

private def mkCtorPattern
    (_typeName : TSyntax `ident)
    (ctorName : Name)
    (fields   : Array (Name × Term)) :
    CommandElabM (TSyntax `term) := do
  let ctorName := mkIdent ctorName
  let argPats ← fields.mapM fun (name, ty) => mkPatArg name ty
--   if argPats.isEmpty then
--     `(term| $typeName:ident.$ctorName:ident)
--   else
  `(term| .$ctorName:ident $argPats*)
    -- let mut pat ← `(term| $(argPats[0]!):term)
    -- for n in [1:argPats.size] do
    --     pat ← `(term| $pat:term $(argPats[n]!):term)
    -- `(term| $typeName:ident.$ctorName:ident $pat:term)

private def mkExecuteAlt
    (typeName : TSyntax `ident)
    (stateIdent : Ident)
    (spec : CtorSpec) :
    CommandElabM (TSyntax ``matchAlt) := do
  let fields := fieldsOfPieces spec.pieces
  let pat ← mkCtorPattern typeName spec.ctorName fields
  let sem := spec.sem
  let rhs : TSyntax `term ← `(term| ($sem:term) $stateIdent)
  `(matchAltExpr| | $pat:term => $rhs:term)

private def mkExecuteCmd
    (typeName : TSyntax `ident)
    (execName : TSyntax `ident)
    (mstateName : TSyntax `ident)
    (specs : Array CtorSpec) :
    CommandElabM (TSyntax `command) := do
  let stateName ← MonadQuotation.addMacroScope `_ms
  let instrName ← MonadQuotation.addMacroScope `_instr
  let stateIdent := mkIdent stateName
  let instrIdent := mkIdent instrName
  let regNameIdent := mkIdent `RegisterName
  let uintName := mkIdent `UInt64
  let alts ← specs.mapM (mkExecuteAlt typeName stateIdent)
  `(command|
    def $execName:ident [MachineStateI ($mstateName $typeName) $regNameIdent $uintName $uintName]
                            ($stateIdent : $mstateName $typeName)
                            ($instrIdent : $typeName:ident) : MState $typeName :=
      match $instrIdent:ident with
      $alts:matchAlt*)


/-! ## Top-Level-Elaborator -/

private def elabMakeInstrCore
    (typeName : TSyntax `ident)
    (execName : TSyntax `ident)
    (mstateName : TSyntax `ident)
    (entries : TSyntaxArray `instr_set_entry) :
    CommandElabM Unit := do
  let specs ← entries.mapM mkCtorSpec
  let indCmd ← mkInductiveCmd typeName specs
  let synCmds ← specs.mapM (mkSyntaxCmd typeName)
  let execCmd ← mkExecuteCmd typeName execName mstateName specs

  elabCommand indCmd
  for cmd in synCmds do
    elabCommand cmd
  elabCommand execCmd

def elabMakeInstr : CommandElab := fun stx => do
  match stx with
  | `(command| make_InstrSet $typeName:ident $execName:ident $mstate:ident $entries:instr_set_entry*) =>
      elabMakeInstrCore typeName execName mstate entries
  | _ =>
      throwUnsupportedSyntax

#check Syntax.node

private unsafe def elabMkInstrTypeCore
    (archSpecTerm : TSyntax `term) :
    CommandElabM Unit := do
  let arch : ArchSpec ← liftTermElabM <| do
    let expectedTy := mkConst ``ArchSpec
    let archExpr ← Lean.Elab.Term.elabTerm archSpecTerm (some expectedTy)
    let actualTy ← Lean.Meta.inferType archExpr
    let a ← Lean.Elab.Term.elabTerm archSpecTerm none
    let e ← Meta.whnf a
    logInfo s!"{e.getAppArgs[3]!.getAppFn}"
    logInfo s!"{e.getAppArgs[3]!.getAppArgs[0]!}"
    logInfo s!"{e.getAppArgs[3]!.getAppArgs[2]!}"
    logInfo s!"{e.getAppArgs[3]!.getAppFn}"
    logInfo s!"{e.getAppArgs[3]!.getAppFn}"
    let _ ← Meta.whnf e.getAppArgs[3]!
    unless (← Lean.Meta.isDefEq actualTy expectedTy) do
      throwError s!"`mkInstrType` expected `InstrSet.ArchSpec`, got `{← Lean.Meta.ppExpr actualTy}`"
    let archExpr ← Lean.instantiateMVars archExpr
    if archExpr.hasMVar then
      throwError "`mkInstrType` failed: unresolved metavariables in argument"
    Lean.Meta.evalExpr ArchSpec expectedTy archExpr

  let indCmd ← mkInductiveCmd (mkIdent arch.typeName) arch.specs
  elabCommand indCmd

unsafe def elabMkInstrType : CommandElab := fun stx => do
  match stx with
  | `(command| mkInstrType $archSpecTerm:term) =>
      elabMkInstrTypeCore archSpecTerm
  | _ =>
      throwUnsupportedSyntax

@[command_elab makeInstrSet]
def elabMakeInstrSet : CommandElab :=
  elabMakeInstr

@[command_elab mkInstrTypeCmd]
unsafe def elabMkInstrType' : CommandElab :=
  elabMkInstrType

@[term_elab mkInstrSetTerm]
def elabMkInstrSetTerm' : Lean.Elab.Term.TermElab :=
  elabMkInstrSetTerm

@[term_elab mkInstrSetArchTerm]
def elabMkInstrSetArchTerm : Lean.Elab.Term.TermElab :=
  elabMkInstrSetTerm


def abd : ArchSpec := mkInstrSet RV64 Instr execute
  LoadAddress:
    { syntax : la (a:register), (m:immediate),
      semantics: fun (ms) => (MState.addRegisterAt ms a m).incPc }
  LoadImmediate:
    { syntax : li (a:register), (m:immediate),
      semantics: fun (ms) => (MState.addRegisterAt ms a m).incPc}
  Jump:
    { syntax : j (lbl:label),
      semantics: fun (ms) => (MState.jump ms lbl)}
  PANIC:
    { syntax: PANIC,
      semantics: fun (ms) => (MState.setTerminated ms true)}

#check Lean.TSyntax.mk
#check abd
#eval abd.specs.size
mkInstrType abd
#print Instr


/- Hier kommt die beispielhafte Anwendung. -/
declare_syntax_cat mriscx_label
 -- behaviour := both controls the behavior whether lean parser
 -- wants to parse func name as token / ident
declare_syntax_cat mriscx_Instr (behavior := both)
declare_syntax_cat mriscx_syntax
declare_syntax_cat mriscx_program
declare_syntax_cat mriscx_num_or_iden
declare_syntax_cat hoare

-- this cat is for making it easier to differentiate between single line
-- proofs and hole code snippets. Its specially for specifications.
declare_syntax_cat mriscx_spec

/-
make_instrSet Instr ...
> inductive Instr
> concrete Syntax
> Typeclass execute?
> Typeclass specs?

make_execute
> execute function
> elaboration

make_specs
> instance specs

we alwys have
label: instr*

we know:
instr → la r:register, i:immediate

but how does register or immediate look like?

-/
syntax num : mriscx_num_or_ident

syntax ident : mriscx_num_or_ident

variable {InstrType : Type} (ms : MachineStateI (MState InstrType) RegisterName UInt64 ProgramCounter)

make_InstrSet Instr execute MState
  LoadAddress:
    { syntax : la (a:register), (m:immediate),
      semantics: fun (ms) => (MState.addRegisterAt ms a m).incPc }
  Jump:
    { syntax : j (lbl:label),
      semantics: fun (ms) => (MState.jump ms lbl)}
  PANIC:
    { syntax: PANIC,
      semantics: fun (ms) => (MState.setTerminated ms true)}


class exe (MStateType : Type) where
  LoadAddress : MStateType → RegisterName → UInt64 → MStateType

/-
The labels followed by the instructions
-/
syntax ppDedent(ppDedent(ppLine)) ident ": " mriscx_Instr* : mriscx_label
syntax ppDedent(ppDedent(ppLine)) &"." ident ": " mriscx_Instr* : mriscx_label


syntax "mriscx" withPosition(linebreak)
  mriscx_label*
  ppDedent("end") : mriscx_syntax

syntax mriscx_syntax : term


elab_rules : term
  | `($s:mriscx_syntax) => do Elab.Term.elabTerm (← `(term| 1)) none


variable (imm : UInt64)
#check
    mriscx
        main:
            la x0, imm
    end

#print Instr
-- inductive Instr : Type
-- number of parameters: 0
-- constructors:
-- Instr.LoadAddress : UInt64 → UInt64 → Instr
-- Instr.CopyRegister : UInt64 → UInt64 → Instr
-- Instr.Increment : UInt64 → Instr
-- Instr.AddRegister : UInt64 → UInt64 → UInt64 → Instr
-- Instr.Jump : String → Instr

#print execute
-- def execute : MState Instr → Instr → MState Instr :=
-- fun _ms _instr =>
--   match _instr with
--   | Instr.LoadAddress a m => (fun ms => (ms.addRegisterAt a m).incPc) _ms
--   | Instr.Jump lbl => (fun ms => ms.jump lbl) _ms
--   | Instr.PANIC => (fun ms => ms.setTerminated true) _ms



def l : LabelMap := PMap.empty
def i : InstrMap Instr := (0 ↦ Instr.LoadAddress (RegisterName.mk 1 "x1") 2 ; TMap.empty Instr.PANIC)

def c : Code Instr := {labelMap := l, instrMap := i}
def d : MState Instr := {registers := EmptyRegisters, memory := EmptyMemory, pc := 0,
                          terminated := false, instrCounter := 0, code := c}
#eval (d.addRegisterAt (RegisterName.mk 1 "zero") 12).registers
#eval (execute d (d.code.instrMap.get 0)).registers

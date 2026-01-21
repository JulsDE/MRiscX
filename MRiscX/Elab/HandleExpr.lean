import MRiscX.AbstractSyntax.AbstractSyntax
import Lean
open Lean Meta Elab

/-
This file contains some utility functions when working with expressions
-/

def unwrapWhileCreateLabelmap (e? : Option Expr) (labelmap: Expr) : MetaM Expr :=
  match e? with
  | some arg => pure arg
  | none => throwError s!"Experienced an index out of bounds while trying to create a labelmap
    from expr {labelmap}"


partial def getUInt64FromExpr (e : Expr) : MetaM UInt64 := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``UInt64 1 then
    let val ← Meta.whnf <| e.getArg! 0
    let arg := val.getAppArgs[2]!
    let rawNat  ← Meta.whnf <| arg.getArg! 1
    let n := rawNat.rawNatLit?
    match n with
    | some i => return UInt64.ofNat i
    | _ => throwError "Used the wrong argument to get UInt64 from Expr"
  else if e.isAppOfArity' ``UInt64.ofBitVec 1 then
    let bitVecOfNat := e.getArg! 0
    -- this might fall apart when bitvectors are implemented1 slightly differently,
    -- probably should be refactored
    let bitVectorArg := bitVecOfNat.getArg! 1

    match bitVectorArg.rawNatLit? with
    | some i => return UInt64.ofNat i
    | none => pure ()

    if (bitVectorArg.isAppOfArity' ``OfNat.ofNat 3) then
      let bitVectorArg := bitVectorArg.getArg! 1
      match bitVectorArg.rawNatLit? with
          | some i => return UInt64.ofNat i
          | none => pure ()

    let bitVectorArg ← Meta.whnf <| ←unwrapWhileCreateLabelmap (bitVecOfNat.getAppArgs[1]?) e
    let ofNatArgs ← Meta.whnf <| ← unwrapWhileCreateLabelmap (bitVectorArg.getAppArgs[2]?) e
    let rawNat ← unwrapWhileCreateLabelmap ofNatArgs.getAppArgs[1]? e

    match rawNat.rawNatLit? with
    | some i => return UInt64.ofNat i
    | _ => throwError "Used the wrong argument to get UInt64 from Expr"
  else
    throwError "Not a UInt64 Expression"


partial def getStrFromExpr (e : Expr) : MetaM String := do
  let e ← Meta.whnf e
  match e with
  | Expr.lit (Literal.strVal s) => return s
  | _ => throwError "Expected a string literal"


partial def getLabelMapFromExpr (e : Expr): MetaM LabelMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``PMap.empty 2 then
    return PMap.empty
  else if e.isAppOfArity ``PMap.put 5 then
    let labelNameExpr ← Meta.whnf <| e.getArg! 2
    let labelName ← getStrFromExpr labelNameExpr
    let val ← Meta.whnf <| e.getArg! 3
    let n ← getUInt64FromExpr val
    return PMap.put labelName n (←getLabelMapFromExpr (e.getArg! 4))
  else
    throwError s!"{e} is not a partial map"


partial def getLabelMapExpr (e : Expr): MetaM LabelMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Code.mk 2 then
    let labelMapExpr ← Meta.whnf <| e.getArg! 2
    return ← getLabelMapFromExpr labelMapExpr
  throwError s!"{e} is no Expr of type Code!"


def getArgsAsUIntsOrThrow (args : Array Expr) (n : Nat) : MetaM (List UInt64) := do
  if args.size < n then
    throwError "Expected at least {n} arguments, got {args.size}"
  (List.range n).mapM fun i => getUInt64FromExpr (args[i]!)

def getTwoUIntFromExprValidated (args : Array Expr) : MetaM (UInt64 × UInt64) := do
  if args.size < 2 then
    throwError "Expected at least 2 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!)

def getThreeUIntFromExprValidated (args : Array Expr) : MetaM (UInt64 × UInt64 × UInt64) := do
  if args.size < 3 then
    throwError "Expected at least 3 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!, ←getUInt64FromExpr args[2]!)

def getUIntStringFromExprValidated (args : Array Expr) : MetaM (UInt64 × String) := do
  if args.size < 2 then
    throwError "Expected at least 2 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getStrFromExpr args[1]!)

def getTwoUIntOneStringFromExprValidated (args : Array Expr) :
    MetaM (UInt64 × UInt64 × String) := do
  if args.size < 3 then
    throwError "Expected at least 3 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!, ←getStrFromExpr args[2]!)

def getInstrFromExpr (e : Expr) : MetaM Instr := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Instr.LoadAddress 2 then
    let (reg, addr) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadAddress reg addr
  if e.isAppOfArity ``Instr.LoadImmediate 2 then
    let (reg, val) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadImmediate reg val
  if e.isAppOfArity ``Instr.CopyRegister 2 then
    let (dst, src) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.CopyRegister dst src
  if e.isAppOfArity ``Instr.AddImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.AddImmediate dst reg val
  if e.isAppOfArity ``Instr.Increment 1 then
    let dst ←getUInt64FromExpr e.getAppArgs[0]!
    return Instr.Increment dst
  if e.isAppOfArity ``Instr.AddRegister 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.AddRegister dst reg1 reg2
  if e.isAppOfArity ``Instr.SubImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.SubImmediate dst reg val
  if e.isAppOfArity ``Instr.Decrement 1 then
    let dst ←getUInt64FromExpr e.getAppArgs[0]!
    return Instr.Decrement dst
  if e.isAppOfArity ``Instr.SubRegister 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.SubRegister dst reg1 reg2
  if e.isAppOfArity ``Instr.XorImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.XorImmediate dst reg val
  if e.isAppOfArity ``Instr.XOR 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.XOR dst reg1 reg2
  if e.isAppOfArity ``Instr.LoadWordImmediate 2 then
    let (dst, reg) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadWordImmediate dst reg
  if e.isAppOfArity ``Instr.LoadWordReg 2 then
    let (dst, reg) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadWordReg dst reg
  if e.isAppOfArity ``Instr.StoreWord 2 then
    let (reg, dst) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.StoreWord reg dst
  if e.isAppOfArity ``Instr.Jump 1 then
    let label ← getStrFromExpr e.getAppArgs[0]!
    return Instr.Jump label
  if e.isAppOfArity ``Instr.JumpEq 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpEq reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpNeq 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpNeq reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpGt 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpGt reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpLe 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpLe reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpEqZero 2 then
    let (reg, label) ← getUIntStringFromExprValidated e.getAppArgs
    return Instr.JumpEqZero reg label
  if e.isAppOfArity ``Instr.JumpNeqZero 2 then
    let (reg, label) ← getUIntStringFromExprValidated e.getAppArgs
    return Instr.JumpNeqZero reg label
  return Instr.Panic

partial def getInstrMapFromExpr (e : Expr) : MetaM InstructionMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``TMap.empty 3 then
    return TMap.empty Instr.Panic
  else if e.isAppOfArity ``TMap.put 5 then
    let line ← getUInt64FromExpr <| ← Meta.whnf <| e.getArg! 2
    let instr_expr ← Meta.whnf <| e.getArg! 3
    let instr ← getInstrFromExpr instr_expr
    return TMap.put line instr (←getInstrMapFromExpr (e.getArg! 4))
  else
    throwError s!"{e} is not a partial map"

def getInstrMapFromCodeExpr (e : Expr) : MetaM InstructionMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Code.mk 2 then
    return ← getInstrMapFromExpr (e.getArg! 0)
  throwError "Expected an Expr of type Code"


/- a function to split conjunction and disjunction into its parts -/
partial def splitConjDisj (declType : Expr) : MetaM (TSyntax `rcasesPat) := do
  let e ← Meta.whnf declType
  if e.isAppOfArity `Or 2 then
    let left ← splitConjDisj (←Meta.whnf <| e.getArg! 0)
    let right ← splitConjDisj (←Meta.whnf <| e.getArg! 1)
    return (←`(rcasesPat | ($left | $right)))
  if e.isAppOfArity `And 2 then
    let left ← splitConjDisj (←Meta.whnf <| e.getArg! 0)
    let right ← splitConjDisj (←Meta.whnf <| e.getArg! 1)
    return (←`(rcasesPat | ⟨$left , $right⟩))
  if e.isFVar then
    return (←`(rcasesPat | _))
  if e.isArrow then
    let arr? := e.arrow?
    match arr? with
    | some (_, _) =>
      return (←`(rcasesPat | _))
    | none =>
      throwError s!"{e} is an implication but theres missing an expr"

  return (←`(rcasesPat | _))

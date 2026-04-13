import MRiscX.AbstractSyntax.Registers
import MRiscX.Elab.HandleNumOrIdent
import Lean
open Lean Nat Elab PrettyPrinter


def mkRegisterName (r : RegisterName) :=
  mkApp2
    (mkConst ``RegisterName.mk [])
    (mkApp (mkConst ``RegisterNr.ofNat []) (mkNatLit r.nr))
    (mkStrLit r.name)

def getRegisterNameFromUInt64Expr (r : Expr) : Expr :=
  mkApp2
    (mkConst ``RegisterName.mk [])
    ((mkApp (mkConst ``RegisterNr.ofUInt64 []) (r)))
    (mkApp3
      (mkConst ``toString [levelZero])
      (mkConst ``UInt64 [])
      (mkConst ``instToStringUInt64 [])
      r)

def getCorrespondingRegisterBareName? (r : (TSyntax `register_bare)) : Option RegisterName :=
 match r with
  | `(register_bare | x0) =>
    some (RegisterName.mk 0 "x0")
  | `(register_bare | x1) =>
    some (RegisterName.mk 1 "x1")
  | `(register_bare | x2) =>
    some (RegisterName.mk 2 "x2")
  | `(register_bare | x3) =>
    some (RegisterName.mk 3 "x3")
  | `(register_bare | x4) =>
    some (RegisterName.mk 4 "x4")
  | `(register_bare | x5) =>
    some (RegisterName.mk 5 "x5")
  | `(register_bare | x6) =>
    some (RegisterName.mk 6 "x6")
  | `(register_bare | x7) =>
    some (RegisterName.mk 7 "x7")
  | `(register_bare | x8) =>
    some (RegisterName.mk 8 "x8")
  | `(register_bare | x9) =>
    some (RegisterName.mk 9 "x9")
  | `(register_bare | x10) =>
    some (RegisterName.mk 10 "x10")
  | `(register_bare | x11) =>
    some (RegisterName.mk 11 "x11")
  | `(register_bare | x12) =>
    some (RegisterName.mk 12 "x12")
  | `(register_bare | x13) =>
    some (RegisterName.mk 13 "x13")
  | `(register_bare | x14) =>
    some (RegisterName.mk 14 "x14")
  | `(register_bare | x15) =>
    some (RegisterName.mk 15 "x15")
  | `(register_bare | x16) =>
    some (RegisterName.mk 16 "x16")
  | `(register_bare | x17) =>
    some (RegisterName.mk 17 "x17")
  | `(register_bare | x18) =>
    some (RegisterName.mk 18 "x18")
  | `(register_bare | x19) =>
    some (RegisterName.mk 19 "x19")
  | `(register_bare | x20) =>
    some (RegisterName.mk 20 "x20")
  | `(register_bare | x21) =>
    some (RegisterName.mk 21 "x21")
  | `(register_bare | x22) =>
    some (RegisterName.mk 22 "x22")
  | `(register_bare | x23) =>
    some (RegisterName.mk 23 "x23")
  | `(register_bare | x24) =>
    some (RegisterName.mk 24 "x24")
  | `(register_bare | x25) =>
    some (RegisterName.mk 25 "x25")
  | `(register_bare | x26) =>
    some (RegisterName.mk 26 "x26")
  | `(register_bare | x27) =>
    some (RegisterName.mk 27 "x27")
  | `(register_bare | x28) =>
    some (RegisterName.mk 28 "x28")
  | `(register_bare | x29) =>
    some (RegisterName.mk 29 "x29")
  | `(register_bare | x30) =>
    some (RegisterName.mk 30 "x30")
  | `(register_bare | x31) =>
    some (RegisterName.mk 31 "x31")
  | _ => none

def getCorrespondingRegisterAbiName? (r : (TSyntax `register_abi)) : Option RegisterName :=
  match r with
  | `(register_abi | zero) =>
    some (RegisterName.mk 0 "zero")
  | `(register_abi | ra) =>
    some (RegisterName.mk 1 "ra")
  | `(register_abi | sp) =>
    some (RegisterName.mk 2 "sp")
  | `(register_abi | gp) =>
    some (RegisterName.mk 3 "gp")
  | `(register_abi | tp) =>
    some (RegisterName.mk 4 "tp")
  | `(register_abi | t0) =>
    some (RegisterName.mk 5 "t0")
  | `(register_abi | t1) =>
    some (RegisterName.mk 6 "t1")
  | `(register_abi | t2) =>
    some (RegisterName.mk 7 "t2")
  | `(register_abi | s0) =>
    some (RegisterName.mk 8 "s0")
  | `(register_abi | fp) =>
    some (RegisterName.mk 8 "fp")
  | `(register_abi | s1) =>
    some (RegisterName.mk 9 "s1")
  | `(register_abi | a0) =>
    some (RegisterName.mk 10 "a0")
  | `(register_abi | a1) =>
    some (RegisterName.mk 11 "a1")
  | `(register_abi | a2) =>
    some (RegisterName.mk 12 "a2")
  | `(register_abi | a3) =>
    some (RegisterName.mk 13 "a3")
  | `(register_abi | a4) =>
    some (RegisterName.mk 14 "a4")
  | `(register_abi | a5) =>
    some (RegisterName.mk 15 "a5")
  | `(register_abi | a6) =>
    some (RegisterName.mk 16 "a6")
  | `(register_abi | a7) =>
    some (RegisterName.mk 17 "a7")
  | `(register_abi | s2) =>
    some (RegisterName.mk 18 "s2")
  | `(register_abi | s3) =>
    some (RegisterName.mk 19 "s3")
  | `(register_abi | s4) =>
    some (RegisterName.mk 20 "s4")
  | `(register_abi | s5) =>
    some (RegisterName.mk 21 "s5")
  | `(register_abi | s6) =>
    some (RegisterName.mk 22 "s6")
  | `(register_abi | s7) =>
    some (RegisterName.mk 23 "s7")
  | `(register_abi | s8) =>
    some (RegisterName.mk 24 "s8")
  | `(register_abi | s9) =>
    some (RegisterName.mk 25 "s9")
  | `(register_abi | s10) =>
    some (RegisterName.mk 26 "s10")
  | `(register_abi | s11) =>
    some (RegisterName.mk 27 "s11")
  | `(register_abi | t3) =>
    some (RegisterName.mk 28 "t3")
  | `(register_abi | t4) =>
    some (RegisterName.mk 29 "t4")
  | `(register_abi | t5) =>
    some (RegisterName.mk 30 "t5")
  | `(register_abi | t6) =>
    some (RegisterName.mk 31 "t6")
  | _ =>
    none

def getCorrespondingRegisterName? (r : (TSyntax `register)) : Option RegisterName :=
  match r with
  | `(register | $b:register_bare) =>
    getCorrespondingRegisterBareName? b
  | `(register | $a:register_abi) =>
    getCorrespondingRegisterAbiName? a
  | `(register | x $x:num_or_ident) =>
    match x with
    | `($n:num) =>
      let nra := n.getNat % 32
      let nr : RegisterNr := Fin.mk nra (by
                                            unfold nra
                                            apply Nat.mod_lt
                                            simp)
      some (RegisterName.mk (nr) (s!"{n}"))
    | _ =>
      none
  | _ => none

def getCorrespondingRegisterNr? (r : (TSyntax `register)) :=
  match getCorrespondingRegisterName? r with
  | some n => some n.nr
  | none => none

def getCorrespondingRegisterNameAsTerm (r : (TSyntax `register)) : Term :=
  ⟨r⟩

open Lean Macro

def getRegisterNameAbiAsTerm
    (r : String) :  UnexpandM (Option (TSyntax `register_abi)) := do
  match r with
  | "zero" => return some (←`(register_abi| zero))
  | "ra" => return some (←`(register_abi| ra))
  | "sp" => return some (←`(register_abi| sp))
  | "gp" => return some (←`(register_abi| gp))
  | "tp" => return some (←`(register_abi| tp))
  | "t0" => return some (←`(register_abi| t0))
  | "t1" => return some (←`(register_abi| t1))
  | "t2" => return some (←`(register_abi| t2))
  | "s0" => return some (←`(register_abi| s0))
  | "fp" => return some (←`(register_abi| fp))
  | "s1" => return some (←`(register_abi| s1))
  | "a0" => return some (←`(register_abi| a0))
  | "a1" => return some (←`(register_abi| a1))
  | "a2" => return some (←`(register_abi| a2))
  | "a3" => return some (←`(register_abi| a3))
  | "a4" => return some (←`(register_abi| a4))
  | "a5" => return some (←`(register_abi| a5))
  | "a6" => return some (←`(register_abi| a6))
  | "a7" => return some (←`(register_abi| a7))
  | "s2" => return some (←`(register_abi| s2))
  | "s3" => return some (←`(register_abi| s3))
  | "s4" => return some (←`(register_abi| s4))
  | "s5" => return some (←`(register_abi| s5))
  | "s6" => return some (←`(register_abi| s6))
  | "s7" => return some (←`(register_abi| s7))
  | "s8" => return some (←`(register_abi| s8))
  | "s9" => return some (←`(register_abi| s9))
  | "s10" => return some (←`(register_abi| s10))
  | "s11" => return some (←`(register_abi| s11))
  | "t3" => return some (←`(register_abi| t3))
  | "t4" => return some (←`(register_abi| t4))
  | "t5" => return some (←`(register_abi| t5))
  | "t6" => return some (←`(register_abi| t6))
  | _ => return none

def getRegisterNameBareAsTerm
    (r : String) :  UnexpandM (Option (TSyntax `register_bare)) := do
  match r with
  | "x0" => return some (←`(register_bare | x0))
  | "x1" => return some (←`(register_bare | x1))
  | "x2" => return some (←`(register_bare | x2))
  | "x3" => return some (←`(register_bare | x3))
  | "x4" => return some (←`(register_bare | x4))
  | "x5" => return some (←`(register_bare | x5))
  | "x6" => return some (←`(register_bare | x6))
  | "x7" => return some (←`(register_bare | x7))
  | "x8" => return some (←`(register_bare | x8))
  | "x9" => return some (←`(register_bare | x9))
  | "x10" => return some (←`(register_bare | x10))
  | "x11" => return some (←`(register_bare | x11))
  | "x12" => return some (←`(register_bare | x12))
  | "x13" => return some (←`(register_bare | x13))
  | "x14" => return some (←`(register_bare | x14))
  | "x15" => return some (←`(register_bare | x15))
  | "x16" => return some (←`(register_bare | x16))
  | "x17" => return some (←`(register_bare | x17))
  | "x18" => return some (←`(register_bare | x18))
  | "x19" => return some (←`(register_bare | x19))
  | "x20" => return some (←`(register_bare | x20))
  | "x21" => return some (←`(register_bare | x21))
  | "x22" => return some (←`(register_bare | x22))
  | "x23" => return some (←`(register_bare | x23))
  | "x24" => return some (←`(register_bare | x24))
  | "x25" => return some (←`(register_bare | x25))
  | "x26" => return some (←`(register_bare | x26))
  | "x27" => return some (←`(register_bare | x27))
  | "x28" => return some (←`(register_bare | x28))
  | "x29" => return some (←`(register_bare | x29))
  | "x30" => return some (←`(register_bare | x30))
  | "x31" => return some (←`(register_bare | x31))
  | _ => return none



def getRegisterSyntaxFromStr (s : String) : UnexpandM (TSyntax `register) := do
  match (← getRegisterNameAbiAsTerm s) with
  | none =>
    match (← getRegisterNameBareAsTerm s) with
    | none => throw Unit.unit
    | some h => return ⟨h⟩
  | some l => return ⟨l⟩


def getRegisterNameTerm (t : TSyntax `term) : UnexpandM (TSyntax `register) := do
  match t with
  | `(term | toString $arg) =>
    match arg with
    | `(term | UInt64.ofNat $n:num) =>
      return (←`(register | x $n:num))
    | `(term | $i:ident) =>
      return (←`(register | x $i:ident))
    | _ =>
      dbg_trace s!"{t}"
      throw ()
  | `(term | $s:str) =>
    let regNameStr := s.getString
    let regName ← getRegisterSyntaxFromStr regNameStr
    return (←`(register | $regName))
  | _ =>
    dbg_trace s!"{t}"
    throw ()


def getRegisterTerm (t : TSyntax `term): UnexpandM (TSyntax `register) := do
  match t with
  | `(RegisterName.mk $n $name)
  | `({ nr := $n, name := $name }) =>
      return (← getRegisterNameTerm name)
  | `(UInt64.ofNat $n:num)
  | `($n:num) =>
      return (←`(register | x $n:num))
  | `($i:ident) => do
      let ident ← numOrIdentToSyntax i
      return  (←`(register | x $ident))
  | _ => throw Unit.unit




-- TODO
partial def getCorrespondingRegister (r : (TSyntax `register)) : TermElabM Expr := do
  if let some regs := getCorrespondingRegisterName? r then
    return mkRegisterName regs
  if r.raw.isOfKind `choice then
    let left : TSyntax `register := ⟨r.raw.getArg 0⟩
    try
      return (← getCorrespondingRegister left)
    catch _ =>
      let right : TSyntax `register := ⟨r.raw.getArg 1⟩
      return (← getCorrespondingRegister right)
  match r with
  | `(register | x $n:num_or_ident) =>
      return getRegisterNameFromUInt64Expr (← parseMriscxNumOrIdent n)
  | _ =>
      throwError "Unknown sytnax of category register"

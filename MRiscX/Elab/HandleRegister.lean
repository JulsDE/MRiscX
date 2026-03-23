import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Elab.HandleNumOrIdent
open Lean Elab PrettyPrinter


def mkRegisterNr (nr : RegisterNr) :=
  let n := nr.toNat
  mkApp
    (mkConst ``RegisterNr.ofNat [])
    (mkNatLit n)


def mkRegisterName (r : RegisterName) :=
  let nr := mkRegisterNr r.nr
  mkApp2
    (mkConst ``RegisterName.mk [])
    nr
    (mkStrLit r.name)

def getRegisterNameFromUInt64Expr (r : Expr) : TermElabM Expr := do
  return mkApp2
      (mkConst ``RegisterName.mk [])
      (mkApp
        (mkConst ``RegisterNr.ofUInt64 [])
        r)
      (
        mkApp3
        (mkConst ``toString [levelZero])
        (mkConst ``UInt64 [])
        (mkConst ``instToStringUInt64 [])
        r
      )

def getCorrespondingRegisterName? (r : (TSyntax `mriscx_registers)) : Option RegisterName :=
  match r with
  | `(mriscx_registers | x0) =>
    some (RegisterName.mk RegisterNr.zero "x0")
  | `(mriscx_registers | zero) =>
    some (RegisterName.mk RegisterNr.zero "zero")
  | `(mriscx_registers | x1) =>
    some (RegisterName.mk RegisterNr.one "x1")
  | `(mriscx_registers | ra) =>
    some (RegisterName.mk RegisterNr.one "ra")
  | `(mriscx_registers | x2) =>
    some (RegisterName.mk RegisterNr.two "x2")
  | `(mriscx_registers | sp) =>
    some (RegisterName.mk RegisterNr.two "sp")
  | `(mriscx_registers | x3) =>
    some (RegisterName.mk RegisterNr.three "x3")
  | `(mriscx_registers | gp) =>
    some (RegisterName.mk RegisterNr.three "gp")
  | `(mriscx_registers | x4) =>
    some (RegisterName.mk RegisterNr.four "x4")
  | `(mriscx_registers | tp) =>
    some (RegisterName.mk RegisterNr.four "tp")
  | `(mriscx_registers | x5) =>
    some (RegisterName.mk RegisterNr.five "x5")
  | `(mriscx_registers | t0) =>
    some (RegisterName.mk RegisterNr.five "t0")
  | `(mriscx_registers | x6) =>
    some (RegisterName.mk RegisterNr.six "x6")
  | `(mriscx_registers | t1) =>
    some (RegisterName.mk RegisterNr.six "t1")
  | `(mriscx_registers | x7) =>
    some (RegisterName.mk RegisterNr.seven "x7")
  | `(mriscx_registers | t2) =>
    some (RegisterName.mk RegisterNr.seven "t2")
  | `(mriscx_registers | x8) =>
    some (RegisterName.mk RegisterNr.eight "x8")
  | `(mriscx_registers | s0) =>
    some (RegisterName.mk RegisterNr.eight "s0")
  | `(mriscx_registers | fp) =>
    some (RegisterName.mk RegisterNr.eight "fp")
  | `(mriscx_registers | x9) =>
    some (RegisterName.mk RegisterNr.nine "x9")
  | `(mriscx_registers | s1) =>
    some (RegisterName.mk RegisterNr.nine "s1")
  | `(mriscx_registers | x10) =>
    some (RegisterName.mk RegisterNr.ten "x10")
  | `(mriscx_registers | a0) =>
    some (RegisterName.mk RegisterNr.ten "a0")
  | `(mriscx_registers | x11) =>
    some (RegisterName.mk RegisterNr.eleven "x11")
  | `(mriscx_registers | a1) =>
    some (RegisterName.mk RegisterNr.eleven "a1")
  | `(mriscx_registers | x12) =>
    some (RegisterName.mk RegisterNr.twelve "x12")
  | `(mriscx_registers | a2) =>
    some (RegisterName.mk RegisterNr.twelve "a2")
  | `(mriscx_registers | x13) =>
    some (RegisterName.mk RegisterNr.thirteen "x13")
  | `(mriscx_registers | a3) =>
    some (RegisterName.mk RegisterNr.thirteen "a3")
  | `(mriscx_registers | x14) =>
    some (RegisterName.mk RegisterNr.fourteen "x14")
  | `(mriscx_registers | a4) =>
    some (RegisterName.mk RegisterNr.fourteen "a4")
  | `(mriscx_registers | x15) =>
    some (RegisterName.mk RegisterNr.fifteen "x15")
  | `(mriscx_registers | a5) =>
    some (RegisterName.mk RegisterNr.fifteen "a5")
  | `(mriscx_registers | x16) =>
    some (RegisterName.mk RegisterNr.sixteen "x16")
  | `(mriscx_registers | a6) =>
    some (RegisterName.mk RegisterNr.sixteen "a6")
  | `(mriscx_registers | x17) =>
    some (RegisterName.mk RegisterNr.seventeen "x17")
  | `(mriscx_registers | a7) =>
    some (RegisterName.mk RegisterNr.seventeen "a7")
  | `(mriscx_registers | x18) =>
    some (RegisterName.mk RegisterNr.eighteen "x18")
  | `(mriscx_registers | s2) =>
    some (RegisterName.mk RegisterNr.eighteen "s2")
  | `(mriscx_registers | x19) =>
    some (RegisterName.mk RegisterNr.nineteen "x19")
  | `(mriscx_registers | s3) =>
    some (RegisterName.mk RegisterNr.nineteen "s3")
  | `(mriscx_registers | x20) =>
    some (RegisterName.mk RegisterNr.twenty "x20")
  | `(mriscx_registers | s4) =>
    some (RegisterName.mk RegisterNr.twenty "s4")
  | `(mriscx_registers | x21) =>
    some (RegisterName.mk RegisterNr.twentyone "x21")
  | `(mriscx_registers | s5) =>
    some (RegisterName.mk RegisterNr.twentyone "s5")
  | `(mriscx_registers | x22) =>
    some (RegisterName.mk RegisterNr.twentytwo "x22")
  | `(mriscx_registers | s6) =>
    some (RegisterName.mk RegisterNr.twentytwo "s6")
  | `(mriscx_registers | x23) =>
    some (RegisterName.mk RegisterNr.twentythree "x23")
  | `(mriscx_registers | s7) =>
    some (RegisterName.mk RegisterNr.twentythree "s7")
  | `(mriscx_registers | x24) =>
    some (RegisterName.mk RegisterNr.twentyfour "x24")
  | `(mriscx_registers | s8) =>
    some (RegisterName.mk RegisterNr.twentyfour "s8")
  | `(mriscx_registers | x25) =>
    some (RegisterName.mk RegisterNr.twentyfive "x25")
  | `(mriscx_registers | s9) =>
    some (RegisterName.mk RegisterNr.twentyfive "s9")
  | `(mriscx_registers | x26) =>
    some (RegisterName.mk RegisterNr.twentysix "x26")
  | `(mriscx_registers | s10) =>
    some (RegisterName.mk RegisterNr.twentysix "s10")
  | `(mriscx_registers | x27) =>
    some (RegisterName.mk RegisterNr.twentyseven "x27")
  | `(mriscx_registers | s11) =>
    some (RegisterName.mk RegisterNr.twentyseven "s11")
  | `(mriscx_registers | x28) =>
    some (RegisterName.mk RegisterNr.twentyeight "x28")
  | `(mriscx_registers | t3) =>
    some (RegisterName.mk RegisterNr.twentyeight "t3")
  | `(mriscx_registers | x29) =>
    some (RegisterName.mk RegisterNr.twentynine "x29")
  | `(mriscx_registers | t4) =>
    some (RegisterName.mk RegisterNr.twentynine "t4")
  | `(mriscx_registers | x30) =>
    some (RegisterName.mk RegisterNr.thirty "x30")
  | `(mriscx_registers | t5) =>
    some (RegisterName.mk RegisterNr.thirty "t5")
  | `(mriscx_registers | x31) =>
    some (RegisterName.mk RegisterNr.thirtyone "x31")
  | `(mriscx_registers | t6) =>
    some (RegisterName.mk RegisterNr.thirtyone "t6")
  | `(mriscx_registers | x $x:mriscx_num_or_ident) =>
    match x with
    | `($n:num) =>
      some (RegisterName.mk (RegisterNr.ofNat n.getNat) (s!"{n}"))
    | _ =>
      none
  | _ => none

def getCorrespondingRegisterNr? (r : (TSyntax `mriscx_registers)) :=
  match getCorrespondingRegisterName? r with
  | some n => some n.nr
  | none => none

def getCorrespondingRegisterNameAsTerm (r : (TSyntax `mriscx_registers)) : Term :=
  ⟨r⟩

open Lean Macro

def getRegisterNameAbiAsTerm
    (r : String) :  UnexpandM (Option (TSyntax `mriscx_registers_abi)) := do
  match r with
  | "zero" => return some (←`(mriscx_registers_abi| zero))
  | "ra" => return some (←`(mriscx_registers_abi| ra))
  | "sp" => return some (←`(mriscx_registers_abi| sp))
  | "gp" => return some (←`(mriscx_registers_abi| gp))
  | "tp" => return some (←`(mriscx_registers_abi| tp))
  | "t0" => return some (←`(mriscx_registers_abi| t0))
  | "t1" => return some (←`(mriscx_registers_abi| t1))
  | "t2" => return some (←`(mriscx_registers_abi| t2))
  | "s0" => return some (←`(mriscx_registers_abi| s0))
  | "fp" => return some (←`(mriscx_registers_abi| fp))
  | "s1" => return some (←`(mriscx_registers_abi| s1))
  | "a0" => return some (←`(mriscx_registers_abi| a0))
  | "a1" => return some (←`(mriscx_registers_abi| a1))
  | "a2" => return some (←`(mriscx_registers_abi| a2))
  | "a3" => return some (←`(mriscx_registers_abi| a3))
  | "a4" => return some (←`(mriscx_registers_abi| a4))
  | "a5" => return some (←`(mriscx_registers_abi| a5))
  | "a6" => return some (←`(mriscx_registers_abi| a6))
  | "a7" => return some (←`(mriscx_registers_abi| a7))
  | "s2" => return some (←`(mriscx_registers_abi| s2))
  | "s3" => return some (←`(mriscx_registers_abi| s3))
  | "s4" => return some (←`(mriscx_registers_abi| s4))
  | "s5" => return some (←`(mriscx_registers_abi| s5))
  | "s6" => return some (←`(mriscx_registers_abi| s6))
  | "s7" => return some (←`(mriscx_registers_abi| s7))
  | "s8" => return some (←`(mriscx_registers_abi| s8))
  | "s9" => return some (←`(mriscx_registers_abi| s9))
  | "s10" => return some (←`(mriscx_registers_abi| s10))
  | "s11" => return some (←`(mriscx_registers_abi| s11))
  | "t3" => return some (←`(mriscx_registers_abi| t3))
  | "t4" => return some (←`(mriscx_registers_abi| t4))
  | "t5" => return some (←`(mriscx_registers_abi| t5))
  | "t6" => return some (←`(mriscx_registers_abi| t6))
  | _ => return none

def getRegisterNameBareAsTerm
    (r : String) :  UnexpandM (Option (TSyntax `mriscx_registers_bare)) := do
  match r with
  | "x0" => return some (←`(mriscx_registers_bare | x0))
  | "x1" => return some (←`(mriscx_registers_bare | x1))
  | "x2" => return some (←`(mriscx_registers_bare | x2))
  | "x3" => return some (←`(mriscx_registers_bare | x3))
  | "x4" => return some (←`(mriscx_registers_bare | x4))
  | "x5" => return some (←`(mriscx_registers_bare | x5))
  | "x6" => return some (←`(mriscx_registers_bare | x6))
  | "x7" => return some (←`(mriscx_registers_bare | x7))
  | "x8" => return some (←`(mriscx_registers_bare | x8))
  | "x9" => return some (←`(mriscx_registers_bare | x9))
  | "x10" => return some (←`(mriscx_registers_bare | x10))
  | "x11" => return some (←`(mriscx_registers_bare | x11))
  | "x12" => return some (←`(mriscx_registers_bare | x12))
  | "x13" => return some (←`(mriscx_registers_bare | x13))
  | "x14" => return some (←`(mriscx_registers_bare | x14))
  | "x15" => return some (←`(mriscx_registers_bare | x15))
  | "x16" => return some (←`(mriscx_registers_bare | x16))
  | "x17" => return some (←`(mriscx_registers_bare | x17))
  | "x18" => return some (←`(mriscx_registers_bare | x18))
  | "x19" => return some (←`(mriscx_registers_bare | x19))
  | "x20" => return some (←`(mriscx_registers_bare | x20))
  | "x21" => return some (←`(mriscx_registers_bare | x21))
  | "x22" => return some (←`(mriscx_registers_bare | x22))
  | "x23" => return some (←`(mriscx_registers_bare | x23))
  | "x24" => return some (←`(mriscx_registers_bare | x24))
  | "x25" => return some (←`(mriscx_registers_bare | x25))
  | "x26" => return some (←`(mriscx_registers_bare | x26))
  | "x27" => return some (←`(mriscx_registers_bare | x27))
  | "x28" => return some (←`(mriscx_registers_bare | x28))
  | "x29" => return some (←`(mriscx_registers_bare | x29))
  | "x30" => return some (←`(mriscx_registers_bare | x30))
  | "x31" => return some (←`(mriscx_registers_bare | x31))
  | _ => return none



def getRegisterSyntaxFromStr (s : String) : UnexpandM (TSyntax `mriscx_registers) := do
  match (← getRegisterNameAbiAsTerm s) with
  | none =>
    match (← getRegisterNameBareAsTerm s) with
    | none => throw Unit.unit
    | some h => return ⟨h⟩
  | some l => return ⟨l⟩


def getRegisterNameTerm (t : TSyntax `term) : UnexpandM (TSyntax `mriscx_registers) := do
  match t with
  | `(term | toString $arg) =>
    match arg with
    | `(term | UInt64.ofNat $n:num) =>
      return (←`(mriscx_registers | x $n:num))
    | _ =>
      dbg_trace s!"{t}"
      throw ()
  | `(term | $s:str) =>
    let regNameStr := s.getString
    let regName ← getRegisterSyntaxFromStr regNameStr
    return (←`(mriscx_registers | $regName))
  | _ =>
    dbg_trace s!"{t}"
    throw ()


def getRegisterTerm (t : TSyntax `term): UnexpandM (TSyntax `mriscx_registers) := do
  match t with
  | `(RegisterName.mk (RegisterNr.ofNat $n) $name)
  | `({ nr := $n, name := $name }) =>
      return (← getRegisterNameTerm name)
  | `(UInt64.ofNat $n:num)
  | `($n:num) =>
      return (←`(mriscx_registers | x $n:num))
  | `($i:ident) => do
      let ident ← numOrIdentToSyntax i
      return  (←`(mriscx_registers | x $ident))
  | _ => throw Unit.unit


def getCorrespondingRegister (r : (TSyntax `mriscx_registers)) : TermElabM Expr :=
  match r with
  | `(mriscx_registers | x0) =>
    return mkRegisterName (RegisterName.mk RegisterNr.zero "x0")
  | `(mriscx_registers | zero) =>
    return mkRegisterName (RegisterName.mk RegisterNr.zero "zero")
  | `(mriscx_registers | x1) =>
    return mkRegisterName (RegisterName.mk RegisterNr.one "x1")
  | `(mriscx_registers | ra) =>
    return mkRegisterName (RegisterName.mk RegisterNr.one "ra")
  | `(mriscx_registers | x2)
  | `(mriscx_registers | sp) =>
    return mkUInt64Lit 2
  | `(mriscx_registers | x3)
  | `(mriscx_registers | gp)
  | `(mriscx_registers | x4)
  | `(mriscx_registers | tp)
  | `(mriscx_registers | x5)
  | `(mriscx_registers | t0)
  | `(mriscx_registers | x6)
  | `(mriscx_registers | t1)
  | `(mriscx_registers | x7)
  | `(mriscx_registers | t2)
  | `(mriscx_registers | x8)
  | `(mriscx_registers | s0)
  | `(mriscx_registers | fp)
  | `(mriscx_registers | x9)
  | `(mriscx_registers | s1)
  | `(mriscx_registers | x10)
  | `(mriscx_registers | a0)
  | `(mriscx_registers | x11)
  | `(mriscx_registers | a1)
  | `(mriscx_registers | x12)
  | `(mriscx_registers | a2)
  | `(mriscx_registers | x13)
  | `(mriscx_registers | a3)
  | `(mriscx_registers | x14)
  | `(mriscx_registers | a4)
  | `(mriscx_registers | x15)
  | `(mriscx_registers | a5)
  | `(mriscx_registers | x16)
  | `(mriscx_registers | a6)
  | `(mriscx_registers | x17)
  | `(mriscx_registers | a7)
  | `(mriscx_registers | x18)
  | `(mriscx_registers | s2)
  | `(mriscx_registers | x19)
  | `(mriscx_registers | s3)
  | `(mriscx_registers | x20)
  | `(mriscx_registers | s4)
  | `(mriscx_registers | x21)
  | `(mriscx_registers | s5)
  | `(mriscx_registers | x22)
  | `(mriscx_registers | s6)
  | `(mriscx_registers | x23)
  | `(mriscx_registers | s7)
  | `(mriscx_registers | x24)
  | `(mriscx_registers | s8)
  | `(mriscx_registers | x25)
  | `(mriscx_registers | s9)
  | `(mriscx_registers | x26)
  | `(mriscx_registers | s10)
  | `(mriscx_registers | x27)
  | `(mriscx_registers | s11)
  | `(mriscx_registers | x28)
  | `(mriscx_registers | t3)
  | `(mriscx_registers | x29)
  | `(mriscx_registers | t4)
  | `(mriscx_registers | x30)
  | `(mriscx_registers | t5)
  | `(mriscx_registers | x31)
  | `(mriscx_registers | t6) =>
    return mkUInt64Lit 0
  | `(mriscx_registers | x $n:mriscx_num_or_ident) =>
    return ← getRegisterNameFromUInt64Expr (← parseMriscxNumOrIdent n)
  | _ => throwError "Unkown sytnax of catergory mriscx_registers"

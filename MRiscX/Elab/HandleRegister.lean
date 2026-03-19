import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Elab.HandleNumOrIdent
open Lean Elab

#check @RegisterName.mk

def mkRegisterNr (nr : RegisterNr) :=
  let n := nr.toNat
  mkApp
    (mkConst ``RegisterNr.ofNat! [])
    (mkNatLit n)


#eval mkRegisterNr RegisterNr.eight
#eval mkConst ``RegisterNr.eight

def mkRegisterName (r : RegisterName) :=
  let nr := mkRegisterNr r.nr
  mkApp2
    (mkConst ``RegisterName.mk [])
    nr
    (mkStrLit r.name)


def getCorrespondingRegister (r : (TSyntax `mriscx_registers)) : TermElabM Expr :=
  match r with
  | `(mriscx_registers | x0)
  | `(mriscx_registers | zero) =>
    return mkUIntOfNat 0
  | `(mriscx_registers | x1)
  | `(mriscx_registers | ra) =>
    return mkUInt64Lit 1
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
    return ←parseMriscxNumOrIdent n
  | _ => throwError "Unkown sytnax of catergory mriscx_registers"

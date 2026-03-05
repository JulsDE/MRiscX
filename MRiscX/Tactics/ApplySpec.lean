import Lean
import MRiscX.AbstractSyntax.Instr
import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Elab.HandleNumOrIdent
import MRiscX.Elab.HandleExpr
-- import MRiscX.Tactics.TacticUtil

import MRiscX.Basic
import Mathlib.Data.Set.Basic
open Lean Meta Elab Parser Tactic Syntax Term


private def getSpecTacFromInstr (i : Instr) (pc : UInt64): TacticM (TSyntax `tactic) := do
  match i with
  | Instr.LoadAddress dst addr =>
    return (←`(tactic | apply specification_LoadAddress (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (addr := $(mkNumLit s!"{addr}"))))

  | Instr.LoadImmediate dst val =>
    return (←`(tactic | apply specification_LoadImmediate (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (val := $(mkNumLit s!"{val}"))))

  | Instr.CopyRegister dst src =>
    return (←`(tactic | apply specification_CopyRegister  (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (src := $(mkNumLit s!"{src}"))))

  | Instr.AddImmediate dst reg val =>
    return (←`(tactic | apply specification_AddImmediate  (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (regAddend := $(mkNumLit s!"{reg}"))
                                                          (val := $(mkNumLit s!"{val}"))))

  | Instr.Increment dst =>
    return (←`(tactic | apply specification_Increment (pc := $(mkNumLit s!"{pc}"))
                                                      (dst := $(mkNumLit s!"{dst}"))))

  | Instr.AddRegister dst regAddend1 regAddend2 =>
    return (←`(tactic | apply specification_AddRegister (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regAddend1 :=
                                                          $(mkNumLit s!"{regAddend1}"))
                                                        (regAddend2 :=
                                                          $(mkNumLit s!"{regAddend2}"))))

  | Instr.SubImmediate dst reg imm =>
    return (←`(tactic | apply specification_SubImmediate  (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (regMinuend := $(mkNumLit s!"{reg}"))
                                                          (subtrahend := $(mkNumLit s!"{imm}"))))

  | Instr.Decrement r =>
    return (←`(tactic | apply specification_Decrement (pc := $(mkNumLit s!"{pc}"))
                                                      (dst := $(mkNumLit s!"{r}"))))

  | Instr.SubRegister dst regMinuend regSubtrahend =>
    return (←`(tactic | apply specification_SubRegister (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regMinuend := $(mkNumLit s!"{regMinuend}"))
                                                        (regSubtrahend :=
                                                          $(mkNumLit s!"{regSubtrahend}"))))

  | Instr.XorImmediate dst reg val =>
    return (←`(tactic | apply specification_XorImmediate (pc := $(mkNumLit s!"{pc}"))
                                                             (dst := $(mkNumLit s!"{dst}"))
                                                             (reg := $(mkNumLit s!"{reg}"))
                                                             (val := $(mkNumLit s!"{val}"))))

  | Instr.XOR dst reg1 reg2 =>
    return (←`(tactic | apply specification_XOR (pc := $(mkNumLit s!"{pc}"))
                                                (dst := $(mkNumLit s!"{dst}"))
                                                (reg1 := $(mkNumLit s!"{reg1}"))
                                                (reg2 := $(mkNumLit s!"{reg2}"))))

  | Instr.LoadWordImmediate dst addr =>
    return (←`(tactic | apply specification_LoadWordImmediate (pc := $(mkNumLit s!"{pc}"))
                                                             (dst := $(mkNumLit s!"{dst}"))
                                                             (addr := $(mkNumLit s!"{addr}"))))

  | Instr.LoadWordReg dst regWithAddr =>
    return (←`(tactic | apply specification_LoadWordReg (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regWithAddr :=
                                                          $(mkNumLit s!"{regWithAddr}"))))

  | Instr.StoreWord regWithValue regWithAddr =>
    return (←`(tactic | apply specification_StoreWord (pc := $(mkNumLit s!"{pc}"))
                                                      (regWithValue :=
                                                        $(mkNumLit s!"{regWithValue}"))
                                                      (regWithAddr :=
                                                        $(mkNumLit s!"{regWithAddr}"))))

  | Instr.Jump lbl =>
    return (←`(tactic | apply specification_Jump (pc := $(mkNumLit s!"{pc}"))
                                                   (label := $(mkStrLit lbl))))

  | Instr.JumpEq reg1 reg2 lbl =>
    return (←`(tactic | first
                          | apply specification_JumpEq_true (pc := $(mkNumLit s!"{pc}"))
                                                       (r1 := $(mkNumLit s!"{reg1}"))
                                                       (r2 := $(mkNumLit s!"{reg2}"))
                                                       (label := $(mkStrLit lbl))
                          | apply specification_JumpEq_false (pc := $(mkNumLit s!"{pc}"))
                                                       (r1 := $(mkNumLit s!"{reg1}"))
                                                       (r2 := $(mkNumLit s!"{reg2}"))
                                                       (label := $(mkStrLit lbl))
                                                    ))
  | Instr.JumpNeq reg1 reg2 lbl =>
    return (←`(tactic | first
                        | apply specification_JumpNeq_true  (pc := $(mkNumLit s!"{pc}"))
                                                            (reg1 := $(mkNumLit s!"{reg1}"))
                                                            (reg2 := $(mkNumLit s!"{reg2}"))
                                                            (label := $(mkStrLit lbl))
                        | apply specification_JumpNeq_false (pc := $(mkNumLit s!"{pc}"))
                                                            (reg1 := $(mkNumLit s!"{reg1}"))
                                                            (reg2 := $(mkNumLit s!"{reg2}"))
                                                            (label := $(mkStrLit lbl))
                                                          ))

  | Instr.JumpGt reg1 reg2 lbl =>
    return (←`(tactic | first
                        | apply specification_JumpGt_true (pc := $(mkNumLit s!"{pc}"))
                                                          (r1 := $(mkNumLit s!"{reg1}"))
                                                          (r2 := $(mkNumLit s!"{reg2}"))
                                                          (label := $(mkStrLit lbl))
                        | apply specification_JumpGt_false  (pc := $(mkNumLit s!"{pc}"))
                                                            (r1 := $(mkNumLit s!"{reg1}"))
                                                            (r2 := $(mkNumLit s!"{reg2}"))
                                                            (label := $(mkStrLit lbl))
                                                         ))

  | Instr.JumpLe reg1 reg2 lbl =>
    return (←`(tactic | first
                          | apply specification_JumpLe_true (pc := $(mkNumLit s!"{pc}"))
                                                            (r1 := $(mkNumLit s!"{reg1}"))
                                                            (r2 := $(mkNumLit s!"{reg2}"))
                                                            (label := $(mkStrLit lbl))
                          | apply specification_JumpLe_false  (pc := $(mkNumLit s!"{pc}"))
                                                              (r1 := $(mkNumLit s!"{reg1}"))
                                                              (r2 := $(mkNumLit s!"{reg2}"))
                                                              (label := $(mkStrLit lbl))
                                                            ))

  | Instr.JumpEqZero reg lbl =>
    return (←`(tactic | first
                          | apply specification_JumpEqZero_true (pc := $(mkNumLit s!"{pc}"))
                                                                (r := $(mkNumLit s!"{reg}"))
                                                                (label := $(mkStrLit lbl))
                          | apply specification_JumpEqZero_false  (pc := $(mkNumLit s!"{pc}"))
                                                                  (r := $(mkNumLit s!"{reg}"))
                                                                  (label := $(mkStrLit lbl))
                                                                ))
  | Instr.JumpNeqZero reg lbl =>
    return (←`(tactic | first
                        | apply specification_JumpNeqZero_true  (pc := $(mkNumLit s!"{pc}"))
                                                                (r := $(mkNumLit s!"{reg}"))
                                                                (label := $(mkStrLit lbl))
                        | apply specification_JumpNeqZero_false  (pc := $(mkNumLit s!"{pc}"))
                                                                 (r := $(mkNumLit s!"{reg}"))
                                                                 (label := $(mkStrLit lbl))
                                                                ))

  | Instr.Panic =>
    throwError "Cannot apply a specification for the instruction `Panic`"



elab "apply_spec'" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let pcAs ← Meta.whnf (←findHypTypeM ctx `h_pc)
    let pcAsExpr := pcAs.getAppArgs[2]!
    let pc ← getUInt64FromExpr pcAsExpr
    let codeEqExpr ← Meta.whnf (←findHypTypeM ctx `h_code')
    let codeExpr := codeEqExpr.getArg! 2
    let instrToSplit ← getInstrFromCodeExpr codeExpr (pc)
    let instr ← getInstrFromExpr instrToSplit
    logInfo s!"{←getSpecTacFromInstr instr pc}"
  -- TODO
    evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s)
      $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `user_precondition)))
    evalTactic (← `(tactic | rw [← $(mkIdent `h_code')] ))
    evalTactic (← `(tactic | split_condis in $(mkIdent `user_precondition) ))
    evalTactic (←getSpecTacFromInstr instr pc)
    evalTactic (← `(tactic | simp ))
    evalTactic (← `(tactic | simp ))
    evalTactic (← `(tactic | simp_currInstr ))
    evalTactic (← `(tactic | exact $(mkIdent `h_pc) ))
    evalTactic (← `(tactic | try simp_t_update))


example:
    mriscx
      first:  xor x 0, x 0, x 1
              li x 1, 0
              la x 2, 0x123
    end
    -- Assert assignment of register as precondition
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = x[0] ^^^ x[1] ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by
  auto_seq
  . auto_seq
    . have : (({n:UInt64 | n = 0} ∪ {n : UInt64 | n > 3} ∪ {3} ∪ {2}) = {n : UInt64 | n ≠ 1})
                := by
                simp_set_eq
      rw [this]
      -- intros h_inter h_empty s h_code' h_pc user_precondition
      apply_spec'
      simp [t_update_neq, t_update_eq]
      simp
      simp [t_update_neq, t_update_eq]
      assumption
      assumption
    . apply_spec specification_LoadImmediate (r := 1) (pc := 1) (v := 0)
  . apply_spec specification_LoadAddress (r := 2) (pc := 2) (v := 0x123)

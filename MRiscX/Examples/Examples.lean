import MRiscX.Basic

/-
New Code Proofs
-/

/-
This is the general notation of a Hoare triple in MRiscX.
r₁, r₂, r₃ represent the registers, respectively.
v₁, v₂ are values that we want to load into the registers.
P is the precondition, and Q represents the postcondition.
l is the line that the program counter points to before the
  first instruction is executed.
L_W represents the whitelist, that is, the set of lines that the
  program counter may point to after program termination.
L_B represents the blacklist, a set of lines that must not be visited
  during runtime.
mriscx_code represents some risc-v like assembly, which can be written
  within the keywords `mriscx` ... `end`.
-/
example (r₁ r₂ r₃ v₁ v₂ : UInt64)
        (P Q : Prop) (l : UInt64)
        (L_W L_B : Set UInt64):
  mriscx
    main:
          li x r₁, v₂
          li x r₂, v₂
          xor x r₃, x r₁, x r₂
          j _store

    _some_label:
          addi x r₁, x 0, 42
  end
  ⦃P⦄ l ↦ ⟨L_W | L_B⟩ ⦃Q⦄
  := by sorry




/-
An example of the first block of the otp implementation from `OtpProof.lean`.
We can use either actual numbers or variables as registers or values.
-/
example (p k c l : UInt64) :
    mriscx
      first:
          la x 0, p
          la x 1, k
          la x 2, c
          li x 3, l
    end
    /-
    The precondition ¬⸨terminated⸩ is a quite common one, as it assert that the terminated
    flag is false. Only then, the machinestate is in a legal state and the next instruction
    can be executed.
    -/
    ⦃¬⸨terminated⸩⦄
    /-
    The entry point of the program is the label **`first`**. As shown, label names can be used
    directly in Hoare triples as strings; during elaboration, these label names are resolved
    to concrete line numbers.

    The program currently looks as follows:
    mriscx
      first:
    line 0:  la x 0, p
    line 1:  la x 1, k
    line 2:  la x 2, c
    line 3:  li x 3, l

    line 4  ...
    end
    The goal is to stop execution after the instruction `li x 3, l`, with the program counter
    pointing to line 4. During execution, no lines other than 0–3 should be visited.


    However, the Hoare-style logic mathcal{L}_{AS} by Lundberg et al. treats the state
    before the first instruction is executed as the state where the program counter already
    points to line 0, and it only considers states after at least one execution step.
    Therefore, to prevent control flow from jumping back to the initial instruction, we must
    add line 0 (corresponding to the label `first`) to the blacklist. This guarantees that
    line 0 is not revisited during execution.
    Also, because the program counter points to line 4 after the execution of `li x 3, l`,
    we want to add n : UInt64 | n > 4 to the blacklist.
    -/
    "first" ↦ ⟨{"first" + 4} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > ("first" + 4)})⟩
    /-
    This postcondition asserts, that the registers have the correct values and addresses loaded
    after executing the program. Also, the machine state still is in a legal state since no
    illegal instruction was executed and we did not visit any line, which holds no instruction.

    In the current version, it is necessary to put the preconditions and postconditions in
    parentheses, with the exception of `¬⸨terminated⸩` (e.G.
    ⦃**(** x[0] = ∧ x[1] = 1 **)** ∧ ¬⸨terminated⸩⦄), in order to successfully apply the
    specification.
    -/
    ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c ∧ x[3] = l) ∧ ¬⸨terminated⸩⦄
  := by
  /- Too peel off the last instruction in order to be able to inspect that individually, we
    apply s_apply_seq''', a custom tactic which applies the rule `S-SEQ` and automatically
    solves some trivial goals. -/
  sapply_s_seq P := ⦃¬⸨terminated⸩⦄ ,
                  R := ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c) ∧ ¬⸨terminated⸩⦄,
                  L_W := {3},
                  L_W' := {4},
                  L_B := ({n:UInt64| n > 3} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 4})
  . sapply_s_seq P := ⦃¬⸨terminated⸩⦄,
                    R := ⦃(x[0] = p ∧ x[1] = k) ∧ ¬⸨terminated⸩⦄,
                    L_W := {2},
                    L_W' := {3},
                    L_B := ({n:UInt64| n > 2} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 3})
    . sapply_s_seq -- P := ⦃¬⸨terminated⸩⦄ → can be omitted
                      R := ⦃(x[0] = p) ∧ ¬⸨terminated⸩⦄,
                      L_W := {1},
                      L_W' := {2},
                      L_B := ({n:UInt64| n ≠ 1}),
                      L_B' := ({n:UInt64| n ≠ 2})
      /- At this point, every instruction was isolated. Now we just have to show
        the correctness of each single instruction.
        We can do this, by applying the specification of the instruction respectively.
        For this, the tactic apply_spec can be used. This custom tactic applies the
        specification and handles the generated goals.
        To apply the specification, we have to provide some values.
          l := The line the programcounter currently points to.
          r := The register which is being modified.
          v := The value we want to load into the register.
        The parameters differ to each specification.1 -/
      . apply_spec specification_LoadAddress (l := 0) (r := 0) (v := p)
      . apply_spec specification_LoadAddress (l := 1) (r := 1) (v := k)
    . apply_spec specification_LoadAddress (l := 2) (r := 2) (v := c)
  . apply_spec specification_LoadImmediate (l := 3) (r := 3) (v := l)

/- A function to avoid repetition while writing the hoare-triples -/
def pairwiseDistinct (r₁ r₂ r₃ r₄ : UInt64) :=
  r₁ ≠ r₂
  ∧ r₁ ≠ r₃
  ∧ r₁ ≠ r₄
  ∧ r₂ ≠ r₃
  ∧ r₂ ≠ r₄
  ∧ r₃ ≠ r₄

/-
Use variables for registers and addresses / values
-/
example (r₁ r₂ r₃ r₄ : UInt64) (p k c l : UInt64) :
    mriscx
      first:
            la x r₁, p
            la x r₂, k
            la x r₃, c
            li x r₄, l
    end
    ⦃
      pairwiseDistinct r₁ r₂ r₃ r₄
      ∧ ¬⸨terminated⸩
    ⦄
    "first" ↦ ⟨{"first" + 4} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > ("first" + 4)})⟩
    ⦃((x[r₁] = p ∧ x[r₂] = k ∧ x[r₃] = c ∧ x[r₄] = l))
      ∧ ¬⸨terminated⸩⦄
  := by
  sapply_s_seq
                  R := ⦃(x[r₁] = p ∧ x[r₂] = k ∧ x[r₃] = c
                        ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                        ∧ ¬⸨terminated⸩⦄,
                  L_W := {3},
                  L_W' := {4},
                  L_B := ({n:UInt64| n > 3} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 4})
  . sapply_s_seq
                    R := ⦃(x[r₁] = p ∧ x[r₂] = k
                          ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                          ∧ ¬⸨terminated⸩⦄,
                    L_W := {2},
                    L_W' := {3},
                    L_B := ({n:UInt64| n > 2} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 3})
    . sapply_s_seq
                      R := ⦃(x[r₁] = p
                            ∧ pairwiseDistinct r₁ r₂ r₃ r₄)
                            ∧ ¬⸨terminated⸩⦄,
                      L_W := {1},
                      L_W' := {2},
                      L_B := ({n:UInt64| n ≠ 1}),
                      L_B' := ({n:UInt64| n ≠ 2})
      . apply_spec specification_LoadAddress (l := 0) (r := r₁) (v := p)
      . apply_spec specification_LoadAddress (l := 1) (r := r₂) (v := k)
    . apply_spec specification_LoadAddress (l := 2) (r := r₃) (v := c)
  . apply_spec specification_LoadImmediate (l := 3) (r := r₄) (v := l)




example:
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end
    -- Assert assignment of register as precondition
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by
  /-
  apply s_seq with automatically solve set equality
  -/
  sapply_s_seq  P := _ ,
                  R := ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                  L_W := {2},
                  L_W' := {3},
                  L_B := ({n:UInt64| n > 2} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 3})
    /-
    apply s_seq without automatically solve set equality
    -/
  . sapply_s_seq''  R := ⦃(x[0] = 2 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄,
                    L_W := {1},
                    L_W' := {2},
                    L_B := ({n:UInt64| n ≠ 1}),
                    L_B' := ({n:UInt64| n ≠ 2})
    . apply_spec specification_LoadImmediate (l := 0) (r := 0) (v := 2)
    . apply_spec specification_LoadImmediate (l := 1) (r := 1) (v := 0)
    . simp_set_eq
  . apply_spec specification_LoadAddress (l := 2) (r := 2) (v := 0x123)





/-
Use of identifiers of type `Code` in hoare-triple
-/
def code : Code :=
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end

example:
    code
    ⦃¬⸨terminated⸩⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123) ∧ ¬⸨terminated⸩⦄
  := by
  -- Identifier needs to be unfolded
  unfold code
  sapply_s_seq
                  R := ⦃(x[0] = 2 ∧ x[1] = 0 ) ∧ ¬⸨terminated⸩⦄,
                  L_W := {2},
                  L_W' := {3},
                  L_B := ({n:UInt64| n > 2} ∪ {0}),
                  L_B' := ({n:UInt64| n ≠ 3})

  . sapply_s_seq
                    R := ⦃(x[0] = 2) ∧ ¬⸨terminated⸩⦄,
                    L_W := {1},
                    L_W' := {2},
                    L_B := ({n:UInt64| n ≠ 1}),
                    L_B' := ({n:UInt64| n ≠ 2})
    . apply_spec specification_LoadImmediate (l := 0) (r := 0) (v := 2)
    . apply_spec specification_LoadImmediate (l := 1) (r := 1) (v := 0)
  . apply_spec specification_LoadAddress (l := 2) (r := 2) (v := 0x123)




example:
    code
    ⦃¬⸨terminated⸩⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123) ∧ ¬⸨terminated⸩⦄
  := by
  unfold code
  -- use tactic `auto seq` which automatically applies S_SEQ and calcs missing values
  auto seq
  . auto seq
    . have : (({n:UInt64 | n = 0} ∪ {n : UInt64 | n > 3} ∪ {3} ∪ {2}) = {n : UInt64 | n ≠ 1})
                := by
                simp_set_eq
      rw [this]
      apply_spec specification_LoadImmediate (l := 0) (r := 0) (v := 2)
    .apply_spec specification_LoadImmediate (l := 1) (r := 1) (v := 0)
  . apply_spec specification_LoadAddress (r := 2) (l := 2) (v := 291)


#check ⦃x[2] = 12⦄


example:
  mriscx
    first:  li x 0, 6
            li x 1, 123
            xor x 2, x 0, x 1
            la x 3, 0x321
            sw x 2, x 3
  end
  ⦃¬⸨terminated⸩⦄
  "first" ↦ ⟨{"first" + 5} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 5})⟩
  ⦃
    (x[0] = 6 ∧ x[1] = 123 ∧
    x[2] = x[0] ^^^ x[1] ∧ x[3] = 0x321 ∧ mem[x[3]] = x[2]) ∧
    ¬⸨terminated⸩⦄
:= by
  sapply_s_seq
                -- P := P ,
                R := ⦃(x[0] = 6 ∧ x[1] = 123
                      ∧ x[2] = x[0] ^^^ x[1]
                      ∧ x[3] = 0x321)
                      ∧ ¬⸨terminated⸩⦄,
                L_W := {4},
                L_W' := {5},
                L_B := ({n:UInt64| n > 4} ∪ {0}),
                L_B' := ({n:UInt64| n ≠ 5})
  . sapply_s_seq
                    -- P := P ,
                    R := ⦃(x[0] = 6 ∧ x[1] = 123
                          ∧ x[2] = x[0] ^^^ x[1])
                          ∧ ¬⸨terminated⸩⦄,
                    L_W := {3},
                    L_W' := {4},
                    L_B := ({n:UInt64| n > 3} ∪ {0}),
                    L_B' := ({n:UInt64| n ≠ 4})
    . sapply_s_seq
                      -- P := P,
                      R := ⦃(x[0] = 6
                            ∧ x[1] = 123)
                            ∧ ¬⸨terminated⸩⦄,
                      L_W := {2},
                      L_W' := {3},
                      L_B := ({n:UInt64| n > 2} ∪ {0}),
                      L_B' := ({n:UInt64| n ≠ 3})
      . sapply_s_seq
                        -- P := P,
                        R := ⦃(x[0] = 6) ∧ ¬⸨terminated⸩⦄,
                        L_W := {1},
                        L_W' := {2},
                        L_B := ({n:UInt64| n ≠ 1}),
                        L_B' := ({n:UInt64| n ≠ 2})
        . apply_spec specification_LoadImmediate (l := 0) (r := 0) (v := 6)
        . apply_spec specification_LoadImmediate (l := 1) (r := 1) (v := 123)
      . apply_spec specification_XOR (l := 2) (d := 2) (r1 := 0) (r2 := 1)
    . apply_spec specification_LoadAddress (l := 3) (r := 3) (v := 0x321)
  . apply_spec specification_StoreWordImmediate (l := 4) (r := 2) (d := 3)

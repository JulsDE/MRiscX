import MRiscX.ExtendParser.Specifications

#check Assertion

theorem S_SEQ {L_b'': Set ProgramCounter}: ∀(P R Q : Assertion (MState Instr)) (c : (Code Instr))
      (l : ProgramCounter) (L_w L_b L_w' L_b' : Set ProgramCounter),
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  L_w' ∩ L_b' = ∅ →
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
      P R l L_w L_b c →
  (∀ l':UInt64, l' ∈ L_w →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    R Q l' L_w' L_b' c) →
  L_b'' = L_b ∩ L_b' →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w' L_b'' c
  := by
  intros P R Q c l L_w L_b L_w' L_b' TInter TEmpty TInter' T
  unfold hoare_triple_up
  intros HFirst HSecond def_L_b'' _ h_empty' s HCode H_pc pre
  specialize HFirst TInter TEmpty s HCode H_pc pre
  rcases HFirst with ⟨s', ⟨HFirstWeak, HFirstPost, HFirstPc⟩⟩
  unfold weak at HFirstWeak
  simp at HFirstWeak
  simp at HCode
  rcases HFirstWeak with ⟨m, ⟨HFW1, HFW2, HFW3, HFW4⟩⟩
  have HCode' : s'.code = c := by
    rw [<- HCode, <- HFW2]
    unfold MState.getCode
    simp
  simp at *
  specialize HSecond s'.pc HFW3 TInter' h_empty' s' HCode' rfl HFirstPost
  unfold weak at HSecond
  rcases HSecond with ⟨s'', ⟨HSecondWeak, HSecondPost, HSecondPc⟩⟩
  simp at HSecondWeak
  rcases HSecondWeak with ⟨m', ⟨_, HSW2, HSW3, HSW4⟩⟩
  exists s''
  constructor <;> try assumption
  . unfold weak
    -- intros HCode
    exists (m + m')
    constructor <;> try assumption
    . simp [HFW1]
    . constructor <;> try assumption
      . rw [<- HFW2] at HSW2
        simp at HSW2
        exact HSW2
      . constructor <;> try assumption
        . intros m'' Hm''
          rw [def_L_b'']
          rw [MachineStateI_getPc_eq_mstate_getPc, Runnable_runNStep_eq_mstate_runNStep]
          apply MState.run_n_plus_m_intersect <;> try assumption
          repeat (simp ; assumption)
  . constructor <;> try assumption
    .
      rw [def_L_b'']
      simp
      intros _
      exact HSecondPc

theorem S_LOOP {α : Type} [Preorder α] [LT α] [WellFoundedLT α] :
    ∀ (Q C I : Assertion (MState Instr)) (code : (Code Instr)) (l : ProgramCounter)
    (L_w L_b : Set ProgramCounter) (V : (MState Instr) → α),
  l ∉ L_w →
  l ∉ L_b →
  (∀ (x : α),
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun st => C st ∧ I st ∧ V st = x) (fun st => V st < x ∧ I st ∧ st.pc = l)
    l ({l} ∪ L_w) L_b code) →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    (fun st => ¬C st ∧ I st) Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    I Q l L_w L_b code
  := by
  intros Q C I code l L_w L_b V h_l_not_mem_Lw h_l_not_mem_Lb h_true h_false
  unfold hoare_triple_up
  intros h_inter h_nonempty s h_code h_pc hI

  have h_inter' : ({l} ∪ L_w) ∩ L_b = ∅ := by
    rw [Set.union_inter_distrib_right]
    simp
    constructor
    · exact h_l_not_mem_Lb
    · exact h_inter

  have h_nonempty' : ({l} ∪ L_w) ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty, Set.union_nonempty]
    right
    rw [Set.nonempty_iff_ne_empty]
    exact h_nonempty
  sorry

theorem weak_with_less_BL_weakens : ∀ (s s' : MState Instr) (L_w L_b L : Set ProgramCounter) ,
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter s s' L_w L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' L_w (L_b \ L)
  := by
  intros s s' L_w L_b L
  unfold weak
  intros H
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.mem_union, = Set.mem_diff]

theorem BL_SUBSET: ∀ (code : Code Instr) (P Q : Assertion (MState Instr)) (l: ProgramCounter)
    (L_w L_b L : Set ProgramCounter),
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w (L_b \ L) code
:= by
  intros c P Q l L_w L_b L T
  unfold hoare_triple_up
  intros H _ h_LwEmpty s HCode pre H_pc
  have L_b_sub : L_b \ L ⊆ L_b := by
    apply Set.diff_subset
  specialize H T h_LwEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  constructor
  · apply weak_with_less_BL_weakens ; exact H1
  · constructor
    · exact H2
    · apply Set.notMem_subset
      · exact L_b_sub
      · exact H3


theorem weak_L_w_with_L_from_L_b : ∀ (s s' : MState Instr) (L_w L_b L : Set ProgramCounter),
  L ⊆ L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' L_w L_b →
  weak (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    s s' (L_w ∪ L) (L_b \ L)
  := by
  intros s s' L_w L_b L T
  unfold weak
  intros H
  rcases H with ⟨n', ⟨H1, H2, H3, H4⟩⟩
  grind only [= Set.subset_def, = Set.mem_union, = Set.mem_diff]

theorem BL_TO_WL: ∀ (code : Code Instr) (P Q : Assertion (MState Instr)) (l : ProgramCounter)
    (L_w L_b L : Set ProgramCounter),
  L ⊆ L_b →
  L_w ∩ L_b = ∅ → -- TODO This or L ⊄ L_w
  L_w ≠ ∅ →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l L_w L_b code →
  hoare_triple_up (MState Instr) Instr (Code Instr) RegisterName UInt64 ProgramCounter
    P Q l (L_w ∪ L) (L_b \ L) code
  := by
  intros c P Q l L_w L_b L TSub TInter TEmpty
  unfold hoare_triple_up
  intros H _ _ s HCode pre H_pc
  specialize H  TInter TEmpty s HCode pre H_pc
  rcases H with ⟨s', ⟨H1, H2, H3⟩⟩
  exists s'
  unfold weak
  constructor
  · apply weak_L_w_with_L_from_L_b <;> try assumption
  . constructor <;> try assumption
    apply Set.notMem_subset (t := L_b) <;> try assumption
    apply Set.diff_subset



instance : Preorder UInt64 where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp
  le_trans := by apply UInt64.le_trans
  lt_iff_le_not_ge := by
    intros a b
    constructor
    . intros h
      simp
      constructor
      . apply UInt64.le_of_lt h
      . exact h
    . simp


instance : WellFoundedLT UInt64 where
  wf := by
    simpa using (measure (fun x : UInt64 => x.toNat)).wf


def c_hamming_weight :=
  mriscx
    init:
      beq a1, zero, L4
      mv a5, a0
      slli a1, a1, 32
      srli a1, a1, 32
      add a3, a0, a1
      li a0, 0

    L3:
      lbu a4, 0(a5)
      cpop t0, a4
      add a4, a4, t0
      addi a5, a5, 1
      bne a5, a3, L3
    L4:
  end

def ms := {code := c_hamming_weight, registers := EmptyRegisters, memory := EmptyMemory , pc := 0,
            terminated := false: MState Instr}
#eval (ms.runNSteps 200).terminated
#eval (ms.runNSteps 200).registers



#check (2#8).cpop



open Lean Elab Tactic in
elab "prepare_second" : tactic => do
  evalTactic (←`(tactic| intros $(mkIdent `l') $(mkIdent `h_l')))
  let id_hl' := mkIdent `h_l'
  let id_hpc := mkIdent `h_pc
  let id_code := mkIdent `h_code'
  evalTactic (← `(tactic| simp at $id_hl':ident))
  evalTactic (←`(tactic| intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `ms)
                          $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `pre)))
  evalTactic (←`(tactic| try simp at $id_hpc:ident))
  evalTactic (←`(tactic| try simp at $id_code:ident))


open Lean Elab Tactic in
elab "solve_curr" : tactic => do
  evalTactic (←`(tactic| simp))
  evalTactic (←`(tactic| try unfold MState.getCurrInstr))
  evalTactic (←`(tactic| try unfold MState.getCode at $(mkIdent `h_code'):ident))
  evalTactic (←`(tactic| rw [$(mkIdent `h_pc):ident]))
  evalTactic (←`(tactic| try rw [$(mkIdent `h_l'):ident]))
  evalTactic (←`(tactic| rw [$(mkIdent `h_code'):ident]))
  evalTactic (←`(tactic| try unfold RegisterName.ofAbi!_zero ))
  evalTactic (←`(tactic| try unfold RegisterName.ofAbi? ))
  evalTactic (←`(tactic| try unfold RegisterNr.ofAbi? ))
  evalTactic (←`(tactic| try unfold RegisterNr.isAbiName ))
  evalTactic (←`(tactic| try unfold RegisterNr.abiNames))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_ofAbi!" : tactic => do
  evalTactic (←`(tactic| unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_ofAbi!" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterName.ofAbi!_zero RegisterName.ofAbi? RegisterNr.ofAbi? RegisterNr.isAbiName RegisterNr.abiNames RegisterNr.ofNat MRISCX_REG_SIZE at $i:ident))
  evalTactic (←`(tactic| simp))

open Lean Elab Tactic in
elab "unfold_rn_ofUint" : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE))

open Lean Elab Tactic in
elab "unfold_rn_ofUint" &"at" i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofUInt64 MRISCX_REG_SIZE at $i:ident))

open Lean Elab Tactic in
elab "unfold_rn_ofnat" : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofNat MRISCX_REG_SIZE))


open Lean Elab Tactic in
elab "unfold_rn_ofnat" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold RegisterNr.ofNat MRISCX_REG_SIZE at $i:ident ))

open Lean Elab Tactic in
elab "simp_getRegisterAt" &" at " i:ident : tactic => do
  evalTactic (←`(tactic| unfold MState.getRegisterAt at $i:ident ))
  evalTactic (←`(tactic| unfold_rn_ofUint at $i:ident ))
  evalTactic (←`(tactic| simp at $i:ident))


open Lean Elab Tactic in
elab "simp_getRegisterAt" : tactic => do
  evalTactic (←`(tactic| unfold MState.getRegisterAt))
  evalTactic (←`(tactic| unfold_rn_ofUint))
  evalTactic (←`(tactic| simp))

@[simp]
theorem MState.getRegisterAt_incPc (ms : MState Instr) (r : RegisterName) :
    ms.incPc.getRegisterAt r = ms.getRegisterAt r := by
  unfold MState.incPc MState.getRegisterAt
  simp

theorem MState.getRegisterAt_addRegisterAt_ne
    (ms : MState Instr) (rd r : RegisterName) (v : UInt64)
    (h : rd.nr ≠ r.nr) :
    (ms.addRegisterAt rd v).getRegisterAt r = ms.getRegisterAt r := by
  unfold MState.addRegisterAt MState.getRegisterAt
  by_cases hrd : rd.nr = 0
  · simp [hrd]
  · by_cases hr : r.nr = 0
    · simp [hr]
    · simp [hrd, hr]
      apply t_update_neq
      apply RegisterName.register_neq_on_nr
      exact h

/-
# --- Schritt 1: x = x - ((x >> 1) & 0x55555555) ---
    li    t1, 0x55555555
    srli  t0, a0, 1
    and   t0, t0, t1
    sub   a0, a0, t0

# --- Schritt 2: x = (x & 0x33333333) + ((x >> 2) & 0x33333333) ---
    li    t1, 0x33333333
    and   t0, a0, t1         # low  zwei-Bit-Gruppen
    srli  t2, a0, 2
    and   t2, t2, t1         # high zwei-Bit-Gruppen
    add   a0, t0, t2

# --- Schritt 3: x = (x + (x >> 4)) & 0x0F0F0F0F ---
    srli  t0, a0, 4
    add   a0, a0, t0
    li    t1, 0x0F0F0F0F
    and   a0, a0, t1

# --- Schritt 4: x = (x * 0x01010101) >> 24 ---
    li    t1, 0x01010101
    mul   a0, a0, t1
    srli  a0, a0, 24
Falls ihr mul vermeiden wollt (z.B. RV32I ohne M-Erweiterung), ersetzt Schritt 4 durch drei Additionen:

    slli  t0, a0, 8
    add   a0, a0, t0
    slli  t0, a0, 16
    add   a0, a0, t0
    srli  a0, a0, 24
-/
#check (0x0F0F0F0F:UInt64)
#check 0x0F0F0F0F
#check 0x5555555555555555
#check 0x3333333333333333
#check 0x0F0F0F0F0F0F0F0F

def ad : UInt64 :=  123
#check   mriscx
            a :
              li    t1, 1
              srli  t0, a0, 1
              and   t0, t0, t1
              sub   a0, a0, t0

              li    t1, 0x123
              and   t0, a0, t1
              srli  t2, a0, 2
              and   t2, t2, t1
              add   a0, t0, t2

              srli  t0, a0, 4
              add   a0, a0, t0
              li    t1, 1085102592571150095
              and   a0, a0, t1

              srli    t1, a0, 8
              add     a0, a0, t1
              srli    t1, a0, 16
              add     a0, a0, t1
              srli    t1, a0, 32
              add     a0, a0, t1
          end

theorem casestudy :
    mriscx
      a :
        li    t1, 6148914691236517205
        srli  t0, a0, 1
        and   t0, t0, t1
        sub   a0, a0, t0

        li    t1, 3689348814741910323
        and   t0, a0, t1
        srli  t2, a0, 2
        and   t2, t2, t1
        add   a0, t0, t2

        srli  t0, a0, 4
        add   a0, a0, t0
        li    t1, 1085102592571150095
        and   a0, a0, t1

        srli    t1, a0, 8
        add     a0, a0, t1
        srli    t1, a0, 16
        add     a0, a0, t1
        srli    t1, a0, 32
        add     a0, a0, t1
    end
    ⦃¬⸨terminated⸩⦄
    0 ↦ ⟨{20} | {n : ProgramCounter | n > 20 ∨ n = 0}⟩
    ⦃x[a0] = (∑ i : Fin 64, ((x[a0]).toBitVec[i]).toNat) ∧ ¬⸨terminated⸩⦄
    := by
  apply S_SEQ _
  sorry

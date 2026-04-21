import MRiscX.AbstractSyntax.MState
-- import MRiscX.Semantics.Run
-- import MRiscX.Hoare.EvalLabelInHoare
-- import MRiscX.Hoare.HoareAssignmentElab
-- import MRiscX.AbstractSyntax.MState
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra


/-
Hoare core

This file introduces Hoare logic into the MRiscX programming language.
To gain a deeper understanding of Hoare logic,  you can read the
"Hoare" chapter in Software Foundations - Volume 2. Also, the
components of the MRiscX programming language should be familiar,
which can be found in "Syntax.lean".
Because the MRiscX assembly language produces unstructured programs, we can't just use the "plain"
Hoare-Logic. This led us to implement the logic from
LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
In: International Conference on Software Engineering and Formal Methods.
Cham: Springer International Publishing, 2020. S. 193-213.

In essence, we introduce Assertions, which are logical claims about
states—specifically, machine states in this context. Using these
assertions, we define Hoare triples, which make claims about the
state before and after the execution of a command.
This can be used to perform a structured proof later.
-/
variable (Instr : Type) (α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType: Type)



abbrev Assertion (α : Type) [Runnable α] : Type := α → Prop

def Assertion.And [Runnable α] (P Q : Assertion α) : Assertion α := fun st => (P st) ∧ (Q st)
def Assertion.Not [Runnable α] (P : Assertion α) : Assertion α := fun st => ¬(P st)



/--
This **weak** relation, inspired by Lundberg et al. (2020),
is defined over two `MState`s, `s` and `s'`.
Unlike earlier formulations that take a single set of lines `L`,
this relation is parameterized by two sets of lines, `L_w` and `L_b`.

This design has the advantage that the condition `s'.pc ∈ L_w` is already guaranteed
by the relation itself. Since we assume `L_w ∩ L_b = ∅`, it immediately follows that
`s'.pc ∉ L_b` must also hold. Consequently, the explicit postcondition `s'.pc ∈ L_b` in
the *Judgment of* `L_as` could be omitted. However, this simplification has not yet been
applied in the current version.

This relation is defined as follows:

State `s'` is reached from state `s` after exactly `n` steps, where `n > 0`, and the program
counter of `s'` points to a line in `L_w`. Moreover, there exists no `n' ∈ ℕ` with `0 < n' < n`
such that the state reached after `n'` steps from `s` has its program counter in `L_w ∪ L_b`.
In other words, `s'` is the **first** state along the execution path whose program counter lies
in `L_w`.

The **weak** relation is deterministic and partial: a program starting in `s` may never reach a
state whose program counter lies in `L_w`. Additionally, the relation guarantees that no
intermediate state between `s` and `s'` has a program counter in `L_w`.

With the help of this relation, unambiguous statements can be made about the flow of the program.

-/

def weak [Runnable α] [MachineStateI α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType]
          (s s' : α) (L_w L_b : Set ProgramCounterType) : Prop :=
  ∃ (n:Nat), n > 0 ∧ Runnable.runNSteps s n = s' ∧
    (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType s') ∈ L_w ∧
  ∀ (n':Nat), 0 < n' ∧ n' < n →
  (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType) (Runnable.runNSteps s n') ∉ (L_w ∪ L_b)


/--
Inspired by the `judgement of L_{as}` in the paper Lundberg et al. (2020).

Suppose, that `L_w ∩ L_b = ∅` and `L_w ≠ ∅` hold, then the `hoare_triple_up` means:

For all states `s` in which both `P(s)` and `I(s)` are satisfied and whose
program counter points to `l`,
there exists a successor state `s'` for which both the relation
`weak(s, L_w ∪ L_b, s')` and `Q(s')`, `I(s')` and `s'.pc ∉ L_w`
are satisfied.
-/
def hoare_triple_up [h : Runnable α] [m : MachineStateI α InstrType CodeType RegisterNameType
                                          RegisterValType ProgramCounterType]
  (P Q : Assertion α) (l : ProgramCounterType) (L_w L_b : Set ProgramCounterType)
  (c : CodeType)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀  (s : α),
  (MachineStateI.getCode InstrType RegisterNameType RegisterValType ProgramCounterType s) = c →
  (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType s) = l →
  P s →
  ∃ (s' : α),
  (weak α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType s s' L_w L_b) ∧ Q s'
  ∧ (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType s') ∉ L_b


/--
Essentially the same as the `hoare_triple_up`, but instead of inspecting a whole code segment,
this relation only focusses on the instruction which is executed next. This can be used to
reason about single instructions in order to define their specification.
-/
def hoare_triple_up_1 [h : Runnable α]
  [m : MachineStateI α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType]
  (P Q : Assertion α) (l : ProgramCounterType) (L_w L_b : Set ProgramCounterType) (i : InstrType)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀ (s : α), MachineStateI.currInstruction CodeType RegisterNameType RegisterValType ProgramCounterType s = i →
  (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType s) = l →
  P s →
  ∃ (s' : α),
  (weak α InstrType CodeType RegisterNameType RegisterValType ProgramCounterType s s' L_w L_b) ∧ Q s'
  ∧ (MachineStateI.getPc InstrType CodeType RegisterNameType RegisterValType s') ∉ L_b

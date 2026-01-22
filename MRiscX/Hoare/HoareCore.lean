import MRiscX.AbstractSyntax.MState
import MRiscX.Semantics.Run
import MRiscX.Hoare.EvalLabelInHoare
import MRiscX.Hoare.HoareAssignmentElab
import MRiscX.AbstractSyntax.AbstractSyntax
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
abbrev Assertion : Type := MState → Prop


/-
In order to proof the code with the new hoare notation presented in the paper, we need a few
adjustments.
First of all, we are going to define the weak function from the paper
-/

def weak (s s' : MState) (L_w L_b : Set UInt64) (c : Code) : Prop :=
  s.code = c →
  ∃ (n:Nat), n > 0 ∧ s.runNSteps n = s' ∧ (s'.pc) ∈ L_w ∧
  ∀ (n':Nat), 0 < n' ∧ n' < n →
  (s.runNSteps n').pc ∉ (L_w ∪ L_b)

/-
The weak function has two states, s and s′, and a set of lines, L, as arguments.
This function now states the following:
If n steps are taken from state s, state s′ is reached. The PC of s′ points to a row that is an element
of L. Here, n must be greater than 0. Furthermore, there is no number n′ with 0 < n′ < n such that after
n′ steps from state s, state s′ is reached, whose PC also points to a row in L.
The weak function is deterministic and partial, since a program that starts in s may never reach
a state in L. It also guarantees that no intermediate state between s and s′ has an lbl from L.
With the help of this function, clear statements can be made about the flow of the program.

With the weak function at hand, we can define the judgement of \mathcal{L}_{AS}.
-/

def hoare_triple_up (P Q : Assertion) (l : UInt64) (L_w L_b : Set UInt64)
  (c : Code)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀ (s : MState), s.code = c →
  s.pc = l →
  P s →
  ∃ (s' : MState), (weak s s' L_w L_b c) ∧ Q s' ∧ s'.pc ∉ L_b

/-
This definition means as much as:

For all states $s$ in which both $P(s)$ and $I(s)$ are satisfied and whose program counter points to $l$,
there exists a successor state $s'$ for which both the function
$\mathbf{weak}(s, L_W \cup L_B, s')$ and $Q(s')$, $I(s')$, and $\mathbf{lbl}(s') \notin L_W$
are satisfied.
The set of lines $L$ used in weak was defined as the union of the disjoint sets $L_W$ and $L_B$.
From the statement of the $\mathsf{Weak}$ function, $\mathbf{lbl}(s') \in L$, and the statement on
$\mathsf{evaluation\ of\ \mathcal{L}_\text{{AS}}}$, $\mathbf{lbl}(s') \notin L_B$, it follows
that $L_W$ comprises exactly those lines to which the program counter of $s'$ may point after execution.
In contrast, $L_B$ contains those lines to which the program counter must not refer either during or after execution.
-/


/-
With the background to verify the correctness of the interpreter, we need a way to
provide a proof of correctness for a single instruction. These functions can be
used for defining the specifications of each instruction.
-/

def weak_one (s s' : MState) (L_w L_b : Set UInt64) : Prop :=
  s.runNSteps 1 = s' ∧ s'.pc ∈ L_w ∧ s'.pc ∉ L_b

def hoare_triple_up_1 (P Q : Assertion) (l:UInt64) (L_w L_b : Set UInt64) (i : Instr)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀ (s : MState), s.currInstruction = i →
  s.pc = l →
  P s →
  ∃ (s' : MState), (weak s s' L_w L_b s.code) ∧ Q s' ∧ s'.pc ∉ L_b

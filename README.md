# MRiscX

MRiscX aims to provide a low-threshold introduction to the world of formal methods.
To this end, an environment has been developed that allows RISC-V assembly code to be verified in 
Lean using Hoare logic.

## Installation

The project is dependent on mathlib. If mathlib is not present, it will be installed to your project 
automatically after adding this project as a dependeny. 

Add this project to your lakefile.toml like this 

```toml
[[require]]
name = "MRiscX"
git = "git@github.com:JulsDE/MRiscX.git"
rev = "main"
version = "0.1.0"
```
Then, execute 
```bash
lake update 
```
in your project. When finished successfully, restart the `Lean Language Server`  and import
```lean4
import MRiscX.Basic
``` 
into a `.lean` file. After a final `Restart File` you can start using the library. 


## Proving your own code


To perform a proof of correctness, you can create a new file, import
```lean4
import MRiscX.Basic
```

and start by defining the hoare triple.

In general, a hoare triple in MRiscX looks like this: 
```lean4
example (r₁ r₂ r₃ v₁ v₂ : UInt64)
        (P Q : Prop) (l : UInt64)
        (L_W L_B : Set UInt64)
        (mriscx_code : Code) :
  mriscx_code
  ⦃P⦄ l ↦ ⟨L_W | L_B⟩ ⦃Q⦄
```



A concrete example of a code snippet which can be verified: 
```lean4
example:
    mriscx
      first:  li x 0, 2
              li x 1, 0
              la x 2, 0x123
    end
    ⦃¬⸨terminated⸩ ∧ x[4] = 123⦄
    "first" ↦ ⟨{3} | ({n:UInt64 | n = "first"} ∪ {n:UInt64 | n > 3})⟩
    ⦃(x[0] = 2 ∧ x[1] = 0 ∧ x[2] = 0x123 ∧ x[4] = 123) ∧ ¬⸨terminated⸩⦄
  := by
```
As you can see, it is possible to use labelnames as indicator where the programcounter should 
start / finish.

For more examples and explanations, have a look into files inside the 
[example folder](MRiscX/Examples), especially the file 
[`Examples.lean`](MRiscX/Examples/Examples.lean) might be helpful.

 **_NOTE:_** In the current version, it is necessary to put the preconditions and postconditions in parentheses, with the exception of `¬⸨terminated⸩` (e.G. 
⦃**(** x[0] = ∧ x[1] = 1 **)** ∧ ¬⸨terminated⸩⦄), in order to successfully apply the 
specification. 

>**A detailed documentation of this project is currently WIP and will be available as 
soon as possible.**

## Structure of the project
- `MRiscX/`
  Contains all relevant Lean files of the project.

- `MRiscX/Basic.lean`
  Imports all relevant Lean files of the project. By importing this file once, all necessary files 
    are imported so that Hoare triples can be formulated.

- `MRiscX/AbstractSyntax`
  Contains all the abstract syntax objects the assembly language essentially bases on 

- `MRiscX/Delab`
  Contains the files responsible for delaboration of assembly language and hoare triple

- `MRiscX/Elab`
  Contains the files handling the elaboration and some specific expr processing  

- `MRiscX/Util`
  Contains some Utility functions like theorems about sets or UInt64 used several times

- `MRiscX/Hoare`
  Contains all the files about the hoare logic and hoare triples

  - `MRiscX/Hoare/HoareAssignmentElab.lean`
    Contains the function 
    `replaceKeywords`, which translates the tokens into corresponding function calls.

  - `MRiscX/Hoare/HoareCore.lean`
    Definition of the central functions `weak` and `hoare_triple_up`.

  - `MRiscX/Hoare/HoareRules.lean`
    Formalization of Hoare rules and their associated proofs.

- `MRiscX/Parser/`
  Contains the syntax definitions of the assembly language and hoare triples 

- `MRiscX/Semantics/`
  Contains files about the semantics of the assembly language 
  
  - `MRiscX/Semantics/Run.lean`
    Contains the `MState.runOneStep` and `MState.runNSteps` functions.

  - `MRiscX/Semantics/Theory.lean`
    Contains basic theorems about properties of machine states.

- `MRiscX/Tactics/`
    Contains all the custom tactics.

  - `MRiscX/Tactics/SplitLastSeq.lean` 
    Contains the logic behind the tactic `auto seq`, which tries to 
    "peel off" the last instruction with appying `S-SEQ` and calculating all the missing values.
  
  - `MRiscX/Tactics/ProofAutomationTacitcs.lean` 
    Contains 
  

- `MRiscX/Examples/`
  Contains some working examples

  - `MRiscX/Examples/Examples.lean`
    Contains many small examples of hoare-triples which are verifyable on correctness pretty easily.

  - `MRiscX/Examples/OtpProof.lean`
    Contains a complete proof of correctness of an implementation of the One-Time-Pad. Individual steps are outsourced to 
    `MRiscX/Examples/singleProofsOTP.lean`.



## Known issues
In the current version, it is necessary to put the preconditions and postconditions in parentheses, with the exception of `¬⸨terminated⸩` (e.G. 
⦃**(** x[0] = ∧ x[1] = 1 **)** ∧ ¬⸨terminated⸩⦄), in order to successfully apply the 
specification. 

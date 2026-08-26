import MRiscX.MonadTrace

-- There is one particular side effect which we are interested in:
-- counting how many times each instruction has been executed.
-- This will be our example for the application of the
-- "monadic run function".

-- helper function that transforms values of
-- type Instr to a type that is suitable as key
-- key = name of constructor
def Instr.toCtorName (instr : Instr) : String :=
  let str := reprStr instr
  match str.splitOn " " with
  | [] => str
  | h :: _ => h

-- Let's create an instance of MonadTrace:
-- HashMap with
-- - key : String (= name of the constructor)
-- - value : Nat (= how many times has instruction been executed)
abbrev InstrStats := Std.HashMap String Nat

def InstrStats.logInstr (instr : Instr) (stats : InstrStats) :=
  let instrStr := instr.toCtorName
  match stats.get? instrStr with
  | none => stats.insert instrStr 1
  | some n => stats.insert instrStr (n + 1)

-- Our MonadTrace is a HashMap InstrStats
-- wrapped inside a state monad.
instance : MonadTraceExtract (StateM InstrStats) Instr where
  extract action := (action.run ∅).1
  trace instr := do set <| (← get).logInstr instr

def InstrStats.pretty (stats : InstrStats) :=
  let entries := stats.toList.mergeSort (· ≤ ·)
  let lines :=
    entries.map fun (k, v) => s!"{k} ↦ {v}"
  "{\n" ++ String.intercalate "\n" lines ++ "\n}"


-- concrete example to test our monadic run function
def code :=
  mriscx
      first:
          la x 0, 0
          la x 1, 1
          la x 2, 2
          li x 3, 3
          j first
    end

def initialState : MState := { DefaultMState with code := code }

-- final execution state can be calculated independent of
-- StateM-interface
#check (runMonadic 10 initialState : StateM InstrStats MState)
#check MonadExtract.extract (runMonadic 10 initialState : StateM InstrStats MState)

#check ((runMonadic 10 initialState : StateM InstrStats MState).run ∅).1

#eval IO.println ((runMonadic 10 initialState : StateM InstrStats MState).run ∅).2.pretty

def calcStats (n : Nat) (c : Code): InstrStats :=
  ((runMonadic n { DefaultMState with code := c} : StateM InstrStats MState).run ∅).2
def calcStatsString (n : Nat) (c : Code): String :=
  calcStats n c
  |> InstrStats.pretty

#eval IO.println <| calcStatsString 100000 code

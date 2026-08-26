-- import MRiscX.AbstractSyntax.Instr
-- import MRiscX.Semantics.Run
import MRiscX.Basic

def Instr.toCtorName (instr : Instr) : String :=
  let str := reprStr instr
  match str.splitOn " " with
  | [] => str
  | h :: _ => h

#eval (Instr.AddRegister 1 2 3).toCtorName


-- key : String, value : Nat
abbrev InstrStats := Std.HashMap String Nat
def InstrStats.inc (instr : Instr) (stats : InstrStats) :=
    let instrStr := instr.toCtorName
  match stats.get? instrStr with
  | none => stats.insert instrStr 1
  | some n => stats.insert instrStr (n + 1)
def InstrStats.pretty (stats : InstrStats) :=
  let entries := stats.toList.mergeSort (· ≤ ·)
  let lines :=
    entries.map fun (k, v) => s!"{k} ↦ {v}"
  "{\n" ++ String.intercalate "\n" lines ++ "\n}"


structure MStateWithStats where
  ms    : MState
  stats : InstrStats

def MStateWithStats.runOneStep (ms : MStateWithStats) : MStateWithStats :=
  if ms.ms.terminated
  then ms
  else
    let instr := ms.ms.currInstruction
    ⟨ ms.ms.runOneStep, ms.stats.inc instr ⟩

def MStateWithStats.run (ms : MStateWithStats) (n : Nat) :=
  Nat.iterate MStateWithStats.runOneStep n ms

def code :=
  mriscx
      first:
          la x 0, 0
          la x 1, 1
          la x 2, 2
          li x 3, 3
          j first
    end

def MyStartState : MStateWithStats := ⟨ { DefaultMState with code := code }, ∅ ⟩

#eval IO.println (MyStartState.run 1000).stats.pretty

instance : Repr MStateWithStats where
  reprPrec ms _ := ms.stats.pretty

-- def measureRunTime (n : Nat) : IO Unit := do
--   let t₁ ← IO.monoMsNow
--   let thunk :=
--     fun _ => (MyStartState.run n)
--   let result := thunk ()
--   let forced := result.stats.size
--   IO.println s!"forced length: {forced}"
--   let t₂ ← IO.monoMsNow
--   IO.println s!"run {n}: {t₂ - t₁} ms"
--   return

-- #eval do
--   let _ ← measureRunTime 2000000

-- Das ist der von ChatGPT vorgeschlagene Weg, um die
-- lazy evaluation auszudrücken und dafür zu sorgen,
-- dass run wirklich zwischen den zwei Zeitmessungen
-- zu Ende ausgewertet wird:
-- eine auf dem Ergebnis von run basierende IO-Aktion durchführen
def forceWithDot (x : Nat) : IO Unit := do
  let s := toString x
  if s.length > 0 then
    IO.print "."
  else
    IO.print "!"

def measureRunTime (n : Nat) : IO (Nat × Nat) := do
  let t₁ ← IO.monoMsNow

  let result := MyStartState.run n
  let forced := result.stats.size
  forceWithDot forced

  let t₂ ← IO.monoMsNow

  -- n, runtime, forced
  return (n, t₂ - t₁) -- wenn ich forced nicht zurückgebe, dann wird das run n nicht wirklich ausgeführt (sondern zu lazy ausgewertet)

def printRuntimeTable (rows : List (Nat × Nat)) : IO Unit := do
  IO.println "n\truntime_ms"
  for (n, runtime) in rows do
    IO.println s!"{n}\t{runtime}"

def measureRunTimes (ns : List Nat) : IO Unit := do
  let mut rows := []
  for n in ns do
    let row ← measureRunTime n
    rows := row :: rows
  IO.println "\n"
  printRuntimeTable rows.reverse

-- #eval measureRunTimes [1000,2000,5000,10000,20000,50000,100000]
-- #eval measureRunTimes [1000,2000,5000,10000,20000,50000,100000,200000,500000,1000000,2000000,5000000]
-- n	runtime_ms
-- 1000	5
-- 2000	11
-- 5000	25
-- 10000	53
-- 20000	106
-- 50000	263
-- 100000	504
-- 200000	971
-- 500000	2378
-- 1000000	4689
-- 2000000	9292
-- 5000000	19144

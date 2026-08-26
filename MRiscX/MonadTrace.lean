import MRiscX.Basic

-- The final state of an execution sequence can be
-- extracted outside of any monad. This way, we
-- can always access the final interpreter state
-- - independently of the chosen trace monad.
class MonadExtract (m : Type → Type)where
  extract : {α : Type} → m α → α

-- ι = type for the instruction set (e.g. ι := Instr)
class MonadTrace (m : Type → Type) (ι : outParam Type) extends Monad m where
  trace : ι → m Unit

class MonadTraceExtract (m : Type → Type) (ι : outParam Type) extends MonadExtract m, MonadTrace m ι


-- MonadTrace adds side effects to the interpreter execution
def runOneStepMonadic {m : Type → Type} [MonadTraceExtract m Instr] (ms : MState) : m MState := do
  if ms.terminated
  then return ms
  else
    let instr := ms.currInstruction
    MonadTrace.trace instr
    return ms.runOneStep

def runMonadic {m : Type → Type} [MonadTraceExtract m Instr] : Nat → MState → m MState
  | 0, ms => pure ms
  | n' + 1, ms => do
    if ms.terminated
      then return ms -- stop as soon as possible -> more efficient
      else
        let instr := ms.currInstruction
        MonadTrace.trace instr
        let ms' := ms.runOneStep
        runMonadic n' ms'

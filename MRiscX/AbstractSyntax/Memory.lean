import MRiscX.AbstractSyntax.Map

/--
Next, the memory address. This address will point to a certain
address in the memory which holds some value
-/
abbrev MemoryAddress := UInt64
abbrev Byte := BitVec 8


abbrev Halfword := BitVec 16
abbrev Word := BitVec 32
abbrev Doubleword := BitVec 64
/--
Definiton of the memory
M := {m_1 ↦ w_1, … , m_k ↦ w_k}
-/


def Memory := TMap MemoryAddress (Byte)
  deriving Repr


/--
MemoryMap with default value 0

M := {m_1 ↦ w_1, … , m_k ↦ w_k ; 0}
-/
def EmptyMemory : Memory := TMap.empty 0

import MRiscX.AbstractSyntax.Registers
import MRiscX.AbstractSyntax.Memory

notation n "*" "Byte" => BitVec (n * 8)

-- What the user should put in
abbrev register_amount := 32
abbrev memory_size := 2^64
abbrev register_size := UInt64
abbrev halfword_size := 2 * Byte
abbrev word_size := 4 * Byte
abbrev doubleword_size := 8 * Byte
abbrev ProgramCounter := UInt64 -- ?


-- What is generated
abbrev register_value := register_size
abbrev register_nr := (Fin register_amount)
abbrev Register := TMap register_nr register_size
abbrev Mem := PMap (Fin memory_size) (1 * Byte)
def empty_registers : TMap register_nr register_value := TMap.empty 0
def empty_mem : PMap (Fin memory_size) (1 * Byte) := PMap.empty




abbrev LabelMap := PMap String ProgramCounter -- generated ?


class MachineState (γ : Type) where
    addRegister : γ → register_nr → register_value → γ
    jump {α β : Type} [BEq α] : γ → PMap α β → α → γ

structure MState where
    register: Register
    memory: Mem
    pc: ProgramCounter

namespace MState

    def addRegister (ms : MState) (r : register_nr) (v : register_value) :=
        {ms with register := ms.register.put r v}

    def getPc (ms : MState) := ms.pc

    def jump (ms : MState) (map : LabelMap) (k : String) :=
        let newPc? := map.get k
        match newPc? with
        | some newPc => {ms with pc := newPc}
        | none => ms

end MState

instance instMState : MachineState MState where
    addRegister := MState.addRegister
    jump  (ms : MState) (map : LabelMap) (k : String) := MState.jump ms (map) k

def DefaultMState := {register := empty_registers, memory := empty_mem, pc := 0 : MState}
#eval DefaultMState.addRegister 0 1


-- make_instr
--     LoadAddress:
--     { syntax : la (a:register), (m:immediate),
--       semantics: fun (ms:MState) => (ms.addRegister a m).incPc }

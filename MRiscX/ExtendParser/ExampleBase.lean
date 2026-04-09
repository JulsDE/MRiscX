-- import MRiscX.AbstractSyntax.Registers
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
abbrev RegisterValue := register_size
abbrev RegisterNr := (Fin register_amount)
abbrev Register := TMap RegisterNr RegisterValue
abbrev Mem := PMap (Fin memory_size) (1 * Byte)
def empty_registers : TMap RegisterNr RegisterValue := TMap.empty 0
def empty_mem : PMap (Fin memory_size) (1 * Byte) := PMap.empty




abbrev LabelMap := PMap String ProgramCounter -- generated ?


class MachineStateI (γ : Type) (RegisterNrType RegisterValType ProgramCounter: Type) where
    addRegister : γ → RegisterNrType → RegisterValType → γ
    setPc : γ → ProgramCounter → γ

abbrev InstrMap (Instr : Type) := TMap UInt64 Instr

structure Code (Instr : Type) where
    labelMap : LabelMap
    codeMap : InstrMap Instr

structure MState (Instr: Type) where
    register: Register
    memory: Mem
    code: Code Instr
    pc: ProgramCounter
    terminated : Bool

namespace MState
    variable {Instr : Type}

    def addRegister (ms : MState Instr) (r : RegisterNr) (v : RegisterValue) :=
        {ms with register := ms.register.put r v}

    def getPc (ms : MState Instr) := ms.pc

    def setPc (ms : MState Instr) (newPc : ProgramCounter) := {ms with pc := newPc}

    def jump (ms : MState Instr) (map : LabelMap) (k : String) :=
        let newPc? := map.get k
        match newPc? with
        | some newPc => {ms with pc := newPc}
        | none => ms

end MState

instance instMState {Instr : Type} : MachineStateI (MState Instr) RegisterNr RegisterValue
                                        ProgramCounter where
    addRegister := MState.addRegister
    setPc := MState.setPc
/-
make_instrSet Instr ...
> inductive Instr
> concrete Syntax
> Typeclass execute?
> Typeclass specs?

make_execute
> execute function
> elaboration

make_specs
> instance specs


(0)
Requirement:
class IMachineState

MachineStateBuilder : Type -> Type

(1)
makeAbstractSyntax (specName, instrTypeName, prefixName)

(2)
Requirement:
InstrType,

makeExecuteTerm / Command

(3)
makeConcreteSyntax

(4)
makeElaboration

(5)
makeDelaboration

(6)
makeHoareSpecs
-/

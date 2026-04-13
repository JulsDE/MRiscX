import MRiscX.AbstractSyntax.Map

abbrev LabelMap := PMap String UInt64

def EmptyLabelMap : LabelMap := PMap.empty

abbrev InstrMap (Instr : Type) := TMap UInt64 Instr

structure Code (Instr : Type) where
  labelMap : LabelMap
  instrMap : InstrMap (Instr)

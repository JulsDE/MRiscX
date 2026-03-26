import MRiscX.AbstractSyntax.AbstractSyntax
import MRiscX.Parser.AssemblySyntax
import MRiscX.Elab.CodeElaborator
import MRiscX.AbstractSyntax.Instr
open Lean PrettyPrinter Delaborator SubExpr Expr Nat

/-
This file contains the delaborator of the code datastructure, which
is implemented as unexpander of the Code.mk function.
-/

def SyntaxInstrMap := TMap UInt64  (TSyntax `mriscx_Instr)
deriving Repr, Inhabited




-- Turn term of function of mriscx_Instr syntax
-- def termToInstr (t: TSyntax `term) : UnexpandM (TSyntax `mriscx_Instr) := do
def termToInstr (t: TSyntax `term) : UnexpandM (TSyntax `mriscx_Instr) := do
  match t with
  | `(Instr.LoadAddress $dst $addr) => do

    let dstName ← getRegisterTerm dst
    let addrNum ← numOrIdentToSyntax addr
    `(mriscx_Instr | la $dstName, $addrNum
    )
  | `(Instr.LoadImmediate $dst $i) =>
    let dstNum ← getRegisterTerm dst
    let iNum  ← numOrIdentToSyntax i
    `(mriscx_Instr | li $dstNum, $iNum
    )
  | `(Instr.LoadNegImmediate $dst $i) =>
    let dstNum ← getRegisterTerm dst
    let iNum  ← numOrIdentToSyntax i
    `(mriscx_Instr | li $dstNum, -$iNum
    )
  | `(Instr.CopyRegister $dst $src) =>
    let dstNum ← getRegisterTerm dst
    let srcNum ← getRegisterTerm src
    `(mriscx_Instr | mv $dstNum, $srcNum
    )
  | `(Instr.AddImmediate $dst $reg $i) =>
    let dstNum ← getRegisterTerm dst
    let regNum ← getRegisterTerm reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | addi $dstNum, $regNum, $iNum
    )
  | `(Instr.AddNegImmediate $dst $reg $i) =>
    let dstNum ← getRegisterTerm dst
    let regNum ← getRegisterTerm reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | addi $dstNum, $regNum, -$iNum
    )
  | `(Instr.Increment $dst) =>
    let dstNum ← getRegisterTerm dst
    `(mriscx_Instr | inc $dstNum
    )
  | `(Instr.AddRegister $dst $reg1 $reg2) =>
    let dstNum ← getRegisterTerm dst
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | add $dstNum, $reg1Num, $reg2Num
    )
  | `(Instr.SubImmediate $dst $reg $i) =>
    let dstNum ← getRegisterTerm dst
    let regNum ← getRegisterTerm reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | subi $dstNum, $regNum, $iNum
    )
  | `(Instr.Decrement $dst) =>
    let dstNum ← getRegisterTerm dst
    `(mriscx_Instr | dec $dstNum
    )
  | `(Instr.SubRegister $dst $reg1 $reg2) =>
    let dstNum ← getRegisterTerm dst
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | sub $dstNum, $reg1Num, $reg2Num
    )

  | `(Instr.XorImmediate $dst $reg $i) =>
    let dstNum ← getRegisterTerm dst
    let regNum ← getRegisterTerm reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | xori $dstNum, $regNum, $iNum
    )

  | `(Instr.XOR $dst $reg1 $reg2) =>
    let dstNum ← getRegisterTerm dst
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | xor $dstNum, $reg1Num, $reg2Num
    )

  | `(Instr.LoadWordImmediate $dst $addr) => do
    let dstNum  ← getRegisterTerm dst
    let addrNum ← numOrIdentToSyntax addr
    `(mriscx_Instr| lw $dstNum, $addrNum:mriscx_num_or_ident
    )

  | `(Instr.LoadWordReg $dst $addr) => do
    let dstNum  ← getRegisterTerm dst
    let addrNum ← getRegisterTerm addr
    -- TODO
    `(mriscx_Instr| lw $dstNum, $addrNum:mriscx_registers
    )

  | `(Instr.StoreWord $reg $dst) =>
    let dstNum ← getRegisterTerm dst
    let regNum ← getRegisterTerm reg
    `(mriscx_Instr | sw $regNum, $dstNum
    )

  | `(Instr.Jump $lbl:ident) => `(mriscx_Instr | j $(mkIdent s!"{lbl}".toName)
  )
  | `(Instr.Jump $lbl:str) => `(mriscx_Instr | j $(mkIdent lbl.getString.toName)
  )
  | `(Instr.JumpEq $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | beq $reg1Num, $reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpEq $reg1 $reg2 $lbl:str) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | beq $reg1Num, $reg2Num, $(mkIdent lbl.getString.toName)
    )

  | `(Instr.JumpNeq $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | bne $reg1Num, $reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpNeq $reg1 $reg2 $lbl:str) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | bne $reg1Num, $reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpGt $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | bgt $reg1Num, $reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpGt $reg1 $reg2 $lbl:str) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | bgt $reg1Num, $reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpLe $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | ble $reg1Num, $reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpLe $reg1 $reg2 $lbl:str) =>
    let reg1Num ← getRegisterTerm reg1
    let reg2Num ← getRegisterTerm reg2
    `(mriscx_Instr | ble $reg1Num, $reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpEqZero $reg $lbl:ident) =>
    let regNum ← getRegisterTerm reg
    `(mriscx_Instr | beqz $regNum, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpEqZero $reg $lbl:str) =>
    let regNum ← getRegisterTerm reg
    `(mriscx_Instr | beqz $regNum, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpNeqZero $reg $lbl:ident) =>
    let regNum ← getRegisterTerm reg
    `(mriscx_Instr | bnez $regNum, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpNeqZero $reg $lbl:str) =>
    let regNum ← getRegisterTerm reg
    `(mriscx_Instr | bnez $regNum, $(mkIdent lbl.getString.toName)
    )
  | _ => return ←`(mriscx_Instr | PANIC!
  )


partial def termToInstrMap (t: TSyntax `term) : UnexpandM SyntaxInstrMap := do
  match t with
  | `(TMap.empty $_) =>
    return (TMap.empty (←`(mriscx_Instr | PANIC!
    )))
  | `((UInt64.ofNat $k:num ↦ $v ; $m)) =>
    return ((UInt64.ofNat k.getNat) ↦ (←termToInstr v) ; (←termToInstrMap m))
  | `(($k:num ↦ $v ; $m)) =>
    return ((UInt64.ofNat k.getNat) ↦ (←termToInstr v) ; (←termToInstrMap m))
  | _ => return TMap.empty (⟨t⟩)


partial def termToLabelMap (t: TSyntax `term) : LabelMap :=
  match t with
  | `(PMap.empty) => PMap.empty
  | `(EmptyLabels) => PMap.empty
  | `(PMap.put $k:str $v:num $m) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | `(p($k:str ↦ UInt64.ofNat $v:num ; $m)) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | `(p($k:str ↦ $v:num ; $m)) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | _ => EmptyLabels




def createLabelInstructionArray (instructionMap:SyntaxInstrMap) (labelMap:LabelMap) :
    Array (String × Array (TSyntax `mriscx_Instr)) := Id.run do
  let labels := labelMap.getKeys

  if labels.length == 1 then do
    let result_lbl := labels.head!
    let mut result_insts := #[]

    for keyInstr in instructionMap.getKeys do
      result_insts := result_insts.push (instructionMap.get keyInstr)

    return #[(result_lbl, result_insts)]


  let mut result := #[]
  for i in [0 : labels.length : 1] do
    let label_entry := labels.get!Internal i
    let label_entry_plus_one := labels.get?Internal (i + 1)

    match label_entry_plus_one with
    | some label_plus_one =>
      let cur_index := labelMap.get label_entry
      let next_index := labelMap.get label_plus_one
      let mut cur_Instrs := #[]

      match cur_index, next_index with
      | some cur, some next => do
        for j in [cur.toNat : next.toNat : 1] do
          cur_Instrs := cur_Instrs.push (instructionMap.get (id j.toUInt64))
        result := result.push (label_entry, cur_Instrs)

      | _, _ => unreachable!

    | none =>
      let cur_index := labelMap.get label_entry
      let last_c_index := instructionMap.getLastKey
      let mut cur_Instrs := #[]

      match cur_index, last_c_index with
      | some cur, some last =>
        for j in [cur.toNat : last.toNat + 1 : 1] do
          cur_Instrs := cur_Instrs.push (instructionMap.get (id j.toUInt64))
        result := result.push (label_entry, cur_Instrs)
      | _ , _ => unreachable!

  return result



@[app_unexpander Code.mk]
def CodeUnexpander : Unexpander
  | `($_ $i $l) => do

    let labels := termToLabelMap l
    let instructionMap := (←termToInstrMap i)
    let syntaxArray := createLabelInstructionArray instructionMap labels

    if syntaxArray.size > 0 then
      let mut syntaxes := #[]

      for labelWithCode in syntaxArray do
        let instrs := labelWithCode.2
        let mut instrSyntaxes := #[]

        for instr in instrs do
          let syntaxInstr := instr
          instrSyntaxes := instrSyntaxes.push (←`(mriscx_Instr | $syntaxInstr))

        if String.Pos.Raw.get labelWithCode.1 0 == '.' then
          let labelName := mkIdent (labelWithCode.1.drop 1).copy.toName
          syntaxes := syntaxes.push (←`(mriscx_label | .$labelName:ident : $instrSyntaxes*))
        else
          let labelName := mkIdent labelWithCode.1.toName
          syntaxes := syntaxes.push (←`(mriscx_label | $labelName:ident : $instrSyntaxes*))
      `(mriscx_syntax | mriscx
        $syntaxes*
        end)
    else
      throw Unit.unit

  | _ => throw Unit.unit

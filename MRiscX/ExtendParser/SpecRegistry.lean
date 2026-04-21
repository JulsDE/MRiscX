import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Lean

inductive POption (α : Prop) where
  | none
  | some (a : α)
deriving Repr , Inhabited

structure Entry where
  prop   : Prop
  proof? : POption prop
deriving Repr, Inhabited

syntax (name := archSpecLookup) term:max "[" str "]" : term

macro_rules (kind := archSpecLookup)
  | `($m[$k:str]) => `(Std.HashMap.get? $m $k)

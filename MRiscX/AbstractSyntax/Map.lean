/-
Maps

These maps are converted from
  title={Software foundations},
  author={Pierce, Benjamin C and Casinghino, Chris and Gaboardi, Marco and Greenberg, Michael
          and Hri{\c{t}}cu, C{\u{a}}t{\u{a}}lin and Sj{\"o}berg, Vilhelm and Yorgey, Brent},
  journal={Webpage: http://www. cis. upenn. edu/bcpierce/sf/current/index. html},
-/

/-
Firstly, we define a total map as recursive type with a key type α and value of type β.
The empty map takes a default value d of type β.
-/
inductive TMap (α : Type) (β : Type) where
  | empty (d : β): TMap α β
  | put (k : α ) (v : β) (t : TMap α β ) : TMap α β
deriving Repr, Inhabited


/-
In order to recieve a value to a given key, we need a
function that searches for key in map.
If the given key is found in map, return corresponding value.
If the key is not found in the map, return the default value.
When there are multiple keys in the map, the last one (the newest) value to that key will be
returned.
This function requires, that the type of the key `α` has the typeclasses BEq and LawfulBEq
implemented.
-/
namespace TMap

  def get {α : Type} [BEq α] [LawfulBEq α] {β : Type} (map : TMap α β) (k : α):=
    match map with
    | TMap.empty d => d
    | TMap.put k' v t => if k == k' then v else TMap.get t k

  def getKeysAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) (list : List α)
      : List α :=
    match map with
    | TMap.empty _ => list
    | TMap.put k _ t => t.getKeysAux (k :: list)

  def getKeys {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : List α :=
    (map.getKeysAux [])

  def getLastKey {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : Option α :=
    match map.getKeys.reverse with
    | List.cons v _ => some v
    | _ => none

  def getValuesAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map: TMap α β) (list : List β)
      : List β :=
    match map with
    | TMap.empty _ => list
    | TMap.put _ v t => t.getValuesAux (v :: list)

    def getValues {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : List β :=
    (map.getValuesAux [])

end TMap

notation:60 "(" k " ↦ "v" ; "m")" => TMap.put k v m


/-
Next, a partial map as recursive type with a key type α and value of type β is defined.
This map does not required a default value d of type β because an option will be returned.
-/
inductive PMap (α : Type) (β : Type) where
  | empty : PMap α β
  | put (k : α ) (v : β) (t : PMap α β )  : PMap α β
deriving Repr, Inhabited

/-
The get-function is also mandatory.
This function differs from the TMap.get by returning corresponding value as option.
If the key is not found in the map, return none.
-/
namespace PMap
  def get {α : Type} {β : Type}[BEq α](map : PMap α β) (k : α) :=
    match map with
    | PMap.empty => none
    | PMap.put k' v t => if k == k' then some v else PMap.get t k

  def getKeysAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : PMap α β) (list : List α)
      : List α :=
    match map with
    | PMap.empty => list
    | PMap.put k _ t => t.getKeysAux (k :: list)

  def getKeys {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : PMap α β) : List α :=
    (map.getKeysAux [])

end PMap

notation:60 "p("k" ↦ "v" ; "m")" => PMap.put k v m

/-
Next are some theorems which are handy for proving statements about the contents of a map.
This theorem states, when a given map [m] which contains the key [i] with the value [v] as last
entry, the TMap.get function returns the corresponding value [v] to key [i].
-/
theorem t_update_eq : forall (α : Type)(β : Type) [BEq α] [LawfulBEq α] (m : TMap α β) (i : α)
    (v : β),
    (i ↦ v ; m).get i = v := by
  intros α β m i v ct
  unfold TMap.get
  simp

/-
If we update a total map [m] at a key [i] and then look up a different key
[j] in the resulting total map, we get the same result that [m] would have
given.
-/
theorem t_update_neq : forall (α : Type) (β : Type)  [BEq α] [LawfulBEq α] (m : TMap α β) (i j : α)
    (v : β),
    i ≠ j -> (i ↦ v ; m).get j = m.get j := by
  intros α β HBEq HLawfulBEq m i j v HNeq
  simp at HNeq
  unfold TMap.get
  cases m ; simp
  . cases HEq: (j==i); simp at HEq
    . simp
      unfold TMap.get
      rfl
    . simp at HEq
      rw[HEq] at HNeq
      exfalso
      apply HNeq
      rfl
  . cases HEq: (j==i); simp at HEq
    . rfl
    . simp at HEq
      rw[HEq] at HNeq
      exfalso
      apply HNeq
      rfl

/-
The same statements like t_update_eq and t_update_neq but for partial maps
-/
theorem p_update_eq : forall (α : Type) (β : Type)  [BEq α] [LawfulBEq α] (m : PMap α β) (i : α)
    (v : β),
    p(i ↦ v ; m).get i = v := by
  intros α β m i v ct
  unfold PMap.get
  simp


theorem p_update_neq : forall (α : Type) (β : Type)  [BEq α] [LawfulBEq α] (m : PMap α β) (i j : α)
    (v : β),
    i != j -> p(i ↦ v ; m).get j = m.get j := by
  intros α β HBEq HLawfulBEq m i j v HNeq
  unfold bne at HNeq
  simp at HNeq
  unfold PMap.get
  cases m ; simp
  . cases HEq: (j==i); simp at HEq
    . simp
      unfold PMap.get
      rfl
    . simp at HEq
      rw[HEq] at HNeq
      exfalso
      apply HNeq
      rfl
  . cases HEq: (j==i); simp at HEq
    . rfl
    . simp at HEq
      rw[HEq] at HNeq
      exfalso
      apply HNeq
      rfl

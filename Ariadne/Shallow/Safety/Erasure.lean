import Ariadne.Shallow.Safety

namespace Ariadne.Shallow.Safety
open Core

inductive ListRelated (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRelated relation [] []
  | cons : relation x y → ListRelated relation xs ys → ListRelated relation (x :: xs) (y :: ys)

theorem ListRelated.length {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) : a.length = b.length := by
  induction related <;> simp_all

theorem ListRelated.append {relation : α → β → Prop} {a c : List α} {b d : List β}
    (left : ListRelated relation a b) (right : ListRelated relation c d) :
    ListRelated relation (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem ListRelated.reverse {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) : ListRelated relation a.reverse b.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using ih.append (.cons head .nil)

theorem ListRelated.map {relation : α → β → Prop} {result : γ → δ → Prop}
    {a : List α} {b : List β} (related : ListRelated relation a b) (f : α → γ) (g : β → δ)
    (step : ∀ x y, relation x y → result (f x) (g y)) : ListRelated result (a.map f) (b.map g) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (step _ _ head) ih

theorem ListRelated.refl (a : List α) : ListRelated Eq a a := by
  induction a with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

theorem ListRelated.eq {a b : List α} (related : ListRelated Eq a b) : a = b := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [head, ih]

def OptionRelated (relation : α → β → Prop) (a : Option α) (b : Option β) : Prop :=
  match a, b with
  | none, none => True
  | some a, some b => relation a b
  | _, _ => False

theorem OptionRelated.isSome {relation : α → β → Prop} {a : Option α} {b : Option β}
    (related : OptionRelated relation a b) : a.isSome = b.isSome := by
  cases a <;> cases b <;> simp_all [OptionRelated]

/-- Guarded and native functions are related by their values on related inputs.
Container relations retain higher-order values rather than replacing callbacks
with functions that forget their guards. -/
def Erases {interp : Named.Interp} : (t : Core.Ty) → Model t interp → t.denote interp → Prop
  | .unit, a, b => a = b
  | .bool, a, b => a = b
  | .int, a, b => a = b
  | .int53, a, b => a = b
  | .number, a, b => a = b
  | .string, a, b => a = b
  | .named _, a, b => a = b
  | .option t, a, b => OptionRelated (Erases t) a b
  | .list t, a, b => ListRelated (Erases t) a b
  | .map k v, a, b => match k with
    | .number | .int | .int53 | .string | .bool =>
      ListRelated (fun a b => a.1 = b.1 ∧ Erases v a.2 b.2) a.entries b.entries
  | .set _, a, b => a = b
  | .pair a b, x, y => Erases a x.1 y.1 ∧ Erases b x.2 y.2
  | .sum a b, x, y => match x, y with
    | .inl x, .inl y => Erases a x y
    | .inr x, .inr y => Erases b x y
    | _, _ => False
  | .fn a b, f, g => ∀ x y, Erases a x y → Erases b (f x).1 (g y)
  | .step s r, x, y => match x, y with
    | .next x, .next y | .stop x, .stop y => Erases s x y
    | .ret x, .ret y => Erases r x y
    | _, _ => False
  | .exit s r, x, y => match x, y with
    | .done x, .done y => Erases s x y
    | .ret x, .ret y => Erases r x y
    | _, _ => False

theorem Erases.key (k : Key) (interp : Named.Interp)
    (a : Model k.type interp) (b : k.type.denote interp) :
    Erases k.type a b ↔ a = cast (by cases k <;> rfl : k.type.denote interp = Model k.type interp) b := by
  cases k <;> rfl

private theorem entries_get [eqκ : BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) :
    OptionRelated relation (MapEntries.get left key) (MapEntries.get right key) := by
  induction related with
  | nil => trivial
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.get, found, OptionRelated] using values
    · simpa [MapEntries.get, found] using ih

theorem unary_erases {interp : Named.Interp} (op : Unary a b) (x : Model a interp) (y : a.denote interp)
    (related : Erases a x y) : Erases b (unary op x) (Denote.unary op y) := by
  cases op
  all_goals first | (solve | simp only [Erases] at related; cases related; rfl) | skip
  case isSome t =>
    cases x <;> cases y <;> simp_all [Erases, OptionRelated, unary, Denote.unary]
  case lengthInt53 t => exact congrArg Int.ofNat related.length
  case length t => exact congrArg Float.Model.ofNat related.length
  case reverse t => exact related.reverse
  case mapSizeInt53 k v =>
    cases k <;> exact congrArg Int.ofNat related.length
  case mapSize k v =>
    cases k <;> exact congrArg Float.Model.ofNat related.length
  case mapKeys k v =>
    cases k <;> exact related.map Prod.fst Prod.fst (fun _ _ h => h.1)
  case mapValues k v =>
    cases k <;> exact related.map Prod.snd Prod.snd (fun _ _ h => h.2)
  case mapEntries k v =>
    cases k <;> exact related
  case setValues k =>
    cases k <;> simp only [Erases] at related ⊢ <;> cases related <;> exact ListRelated.refl _
  case setEntries k =>
    cases k <;> simp only [Erases] at related ⊢ <;> cases related
    all_goals exact (ListRelated.refl _).map (fun a => (a,a)) (fun a => (a,a)) (fun _ _ h => ⟨h,h⟩)

private theorem list_get {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRelated relation left right) (index : Nat) :
    OptionRelated relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => trivial
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index

private theorem entries_set [eqκ : BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) {a : α} {b : β} (value : relation a b) :
    ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2)
      (MapEntries.set left key a) (MapEntries.set right key b) := by
  induction related with
  | nil => exact .cons ⟨rfl, value⟩ .nil
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.set, found] using ListRelated.cons ⟨rfl, value⟩ tail
    · simpa [MapEntries.set, found] using ListRelated.cons ⟨rfl, values⟩ ih

private theorem entries_delete [eqκ : BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) :
    ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2)
      (MapEntries.delete left key) (MapEntries.delete right key) := by
  induction related with
  | nil => exact .nil
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.delete, found] using ih
    · simpa [MapEntries.delete, found] using ListRelated.cons ⟨rfl, values⟩ ih

theorem binary_erases {interp : Named.Interp} (op : Binary a b c)
    (x : Model a interp) (x' : a.denote interp) (y : Model b interp) (y' : b.denote interp)
    (left : Erases a x x') (right : Erases b y y') :
    Erases c (binary op x y) (Denote.binary op x' y') := by
  cases op
  all_goals first | (solve | simp only [Erases] at left right; cases left; cases right; rfl) | skip
  case guard => exact right
  case intRange =>
    simp only [Erases] at left right; cases left; cases right
    exact ListRelated.refl _
  case int53Range =>
    simp only [Erases] at left right; cases left; cases right
    exact ListRelated.refl _
  case append t => exact left.append right
  case get t =>
    simp only [Erases] at right
    cases right
    simp only [binary, Denote.binary, JSArray.get]
    cases indexOf (.number y) with
    | none => trivial
    | some index => simpa only [Option.bind_some, Erases] using list_get left index
  case mapGet k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.get, NumberMap.get]
      first | exact entries_get (eqκ := NumberKey.equality) left y | exact entries_get left y
  case mapHas k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.has, JSMap.get, NumberMap.has, NumberMap.get]
      first
      | exact (entries_get (eqκ := NumberKey.equality) left y).isSome
      | exact (entries_get left y).isSome
  case mapDelete k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.delete, NumberMap.delete, NumberMap.entries]
      first | exact entries_delete (eqκ := NumberKey.equality) left y | exact entries_delete left y
  case setHas k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl
  case setAdd k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl
  case setDelete k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl

theorem mapSet_erases {interp : Named.Interp} (k : Key) {v : Core.Ty}
    (model : Model (.map k v) interp) (native : (Core.Ty.map k v).denote interp)
    (key : Model k.type interp) (nativeKey : k.type.denote interp)
    (value : Model v interp) (nativeValue : v.denote interp)
    (collection : Erases (.map k v) model native) (keys : Erases k.type key nativeKey)
    (values : Erases v value nativeValue) :
    Erases (.map k v) (mapSet k model key value) (Denote.mapSet k native nativeKey nativeValue) := by
  cases k <;> simp only [Erases] at collection keys ⊢ <;> cases keys
  all_goals
    simp only [mapSet, Denote.mapSet, JSMap.set, NumberMap.set, NumberMap.entries]
    first
    | exact entries_set (eqκ := NumberKey.equality) collection _ values
    | exact entries_set collection _ values

def ErasesEnvironment {interp : Named.Interp} (model : Environment Γ interp) (native : Core.Env Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t), Erases t (getVariable v model) (v.get native)

theorem ErasesEnvironment.cons {interp : Named.Interp} {model : Environment Γ interp} {native : Core.Env Γ interp}
    (related : ErasesEnvironment model native) {value : Model t interp} {expected : t.denote interp}
    (equal : Erases t value expected) : ErasesEnvironment (Γ := t :: Γ) (interp := interp) (value, model) (expected, native) := by
  intro u v
  cases v with
  | here => exact equal
  | there v => exact related v

end Ariadne.Shallow.Safety

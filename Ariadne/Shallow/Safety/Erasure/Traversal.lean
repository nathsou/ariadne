import Ariadne.Shallow.Safety.Erasure
import Ariadne.Shallow.Safety.Control

namespace Ariadne.Shallow.Safety
open Core

theorem ListRelated.zipIdx {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (start : Nat) :
    ListRelated (fun a b => relation a.1 b.1 ∧ a.2 = b.2) (a.zipIdx start) (b.zipIdx start) := by
  induction related generalizing start with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.zipIdx_cons] using ListRelated.cons ⟨head, rfl⟩ (ih (start + 1))

theorem ListRelated.mapIdx {relation : α → β → Prop} {result : γ → δ → Prop}
    {a : List α} {b : List β} (related : ListRelated relation a b)
    (f : Nat → α → γ) (g : Nat → β → δ) (step : ∀ i x y, relation x y → result (f i x) (g i y)) :
    ListRelated result (a.mapIdx f) (b.mapIdx g) := by
  induction related generalizing f g with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [List.mapIdx_cons]
    exact .cons (step 0 _ _ head) (ih _ _ (fun i x y h => step (i+1) x y h))

theorem ListRelated.filter {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : α → Bool) (g : β → Bool)
    (step : ∀ x y, relation x y → f x = g y) : ListRelated relation (a.filter f) (b.filter g) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [List.filter_cons, step _ _ head]
    split
    · exact .cons head ih
    · exact ih

theorem ListRelated.any {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : α → Bool) (g : β → Bool)
    (step : ∀ x y, relation x y → f x = g y) : a.any f = b.any g := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons, step _ _ head, ih]

theorem ListRelated.all {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : α → Bool) (g : β → Bool)
    (step : ∀ x y, relation x y → f x = g y) : a.all f = b.all g := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.all_cons, step _ _ head, ih]

theorem ListRelated.find? {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : α → Bool) (g : β → Bool)
    (step : ∀ x y, relation x y → f x = g y) : OptionRelated relation (a.find? f) (b.find? g) := by
  induction related with
  | nil => trivial
  | cons head tail ih =>
    simp only [List.find?_cons, step _ _ head]
    split
    · exact head
    · exact ih

theorem ListRelated.foldl {relation : α → β → Prop} {states : σ → τ → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : σ → α → σ) (g : τ → β → τ)
    (step : ∀ x y s t, relation x y → states s t → states (f s x) (g t y))
    {s : σ} {t : τ} (initial : states s t) : states (a.foldl f s) (b.foldl g t) := by
  induction related generalizing s t with
  | nil => exact initial
  | cons head tail ih => exact ih (step _ _ _ _ head initial)

theorem ListRelated.drop {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (n : Nat) : ListRelated relation (a.drop n) (b.drop n) := by
  induction related generalizing n with
  | nil => simpa using (ListRelated.nil (relation := relation))
  | cons head tail ih =>
    cases n with
    | zero => exact .cons head tail
    | succ n => exact ih n

theorem ListRelated.take {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (n : Nat) : ListRelated relation (a.take n) (b.take n) := by
  induction related generalizing n with
  | nil => simpa using (ListRelated.nil (relation := relation))
  | cons head tail ih =>
    cases n with
    | zero => exact .nil
    | succ n => exact .cons head (ih n)

theorem OptionRelated.map {relation : α → β → Prop} {result : γ → δ → Prop}
    {a : Option α} {b : Option β} (related : OptionRelated relation a b)
    (f : α → γ) (g : β → δ) (step : ∀ x y, relation x y → result (f x) (g y)) :
    OptionRelated result (a.map f) (b.map g) := by
  cases a <;> cases b <;> simp only [OptionRelated] at related
  · trivial
  · exact step _ _ related

theorem call2_erases {interp : Named.Interp} {f : Model (.fn a (.fn b c)) interp}
    {g : (Core.Ty.fn a (.fn b c)).denote interp} (related : Erases (.fn a (.fn b c)) f g)
    {x : Model a interp} {y : a.denote interp} {u : Model b interp} {v : b.denote interp}
    (first : Erases a x y) (second : Erases b u v) : Erases c (call2 f x u).1 (g y v) :=
  related x y first u v second

theorem call3_erases {interp : Named.Interp} {f : Model (.fn a (.fn b (.fn c d))) interp}
    {g : (Core.Ty.fn a (.fn b (.fn c d))).denote interp} (related : Erases (.fn a (.fn b (.fn c d))) f g)
    {x : Model a interp} {y : a.denote interp} {u : Model b interp} {v : b.denote interp}
    {s : Model c interp} {t : c.denote interp}
    (first : Erases a x y) (second : Erases b u v) (third : Erases c s t) :
    Erases d (call3 f x u s).1 (g y v t) := related x y first u v second s t third

theorem listMap_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number b)) interp}
    {g : (Core.Ty.fn a (.fn .number b)).denote interp} {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number b)) f g) (values : Erases (.list a) xs ys) :
    Erases (.list b) ((xs.mapIdx (fun index x => call2 f x (Float.Model.ofNat index))).map Prod.fst)
      (JSArray.map g ys) := by
  rw [map_value]
  exact values.mapIdx _ _ (fun _ _ _ h => call2_erases function h rfl)

theorem listFilter_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number .bool)) interp}
    {g : (Core.Ty.fn a (.fn .number .bool)).denote interp} {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number .bool)) f g) (values : Erases (.list a) xs ys) :
    Erases (.list a) (((xs.mapIdx (fun index x => (x, call2 f x (Float.Model.ofNat index)))).filter
      (fun result => result.2.1)).map Prod.fst) (JSArray.filter g ys) := by
  rw [filter_value]
  apply (values.zipIdx 0).filter _ _ ?_ |>.map Prod.fst Prod.fst (fun _ _ h => h.1)
  intro x y h
  rcases h with ⟨related, equal⟩
  exact call2_erases function related (congrArg Float.Model.ofNat equal)

theorem listSlice_erases {interp : Named.Interp} {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (values : Erases (.list a) xs ys) (start stop : Float.Model) :
    Erases (.list a) (JSArray.slice xs start stop) (JSArray.slice ys start stop) := by
  simp only [JSArray.slice, values.length]
  exact (values.drop _).take _

theorem OptionRelated.eq {a b : Option α} (related : OptionRelated Eq a b) : a = b := by
  cases a <;> cases b <;> simp_all [OptionRelated]

theorem ListRelated.findIdx? {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) (f : α → Bool) (g : β → Bool)
    (step : ∀ x y, relation x y → f x = g y) : a.findIdx? f = b.findIdx? g := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.findIdx?_cons, step _ _ head, ih]

theorem listReduce_erases {interp : Named.Interp} {f : Model (.fn b (.fn a (.fn .number b))) interp}
    {g : (Core.Ty.fn b (.fn a (.fn .number b))).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)}
    {initial : Model b interp} {native : b.denote interp}
    (function : Erases (.fn b (.fn a (.fn .number b))) f g) (values : Erases (.list a) xs ys)
    (start : Erases b initial native) :
    Erases b (xs.zipIdx.foldl (fun (acc, safe) (x, index) =>
      let (result, step) := call3 f acc x (Float.Model.ofNat index)
      (result, safe && step)) (initial, true)).1 (JSArray.reduce g native ys) := by
  have stepEq : (fun (acc, safe) (x, index) =>
      let (result, step) := call3 f acc x (Float.Model.ofNat index)
      (result, safe && step)) =
      (fun (acc, safe) (entry : Model a interp × Nat) =>
        let (result, step) := call3 f acc entry.1 (Float.Model.ofNat entry.2)
        (result, safe && step)) := by
    funext state entry
    cases state; cases entry; rfl
  rw [stepEq, foldl_value (fun acc (entry : Model a interp × Nat) => call3 f acc entry.1 (Float.Model.ofNat entry.2)) xs.zipIdx initial true]
  apply (values.zipIdx 0).foldl _ _ ?_ start
  intro x y s t related states
  exact call3_erases function states related.1 (congrArg Float.Model.ofNat related.2)

theorem listSome_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number .bool)) interp}
    {g : (Core.Ty.fn a (.fn .number .bool)).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number .bool)) f g) (values : Erases (.list a) xs ys) :
    Erases (interp := interp) .bool (search (call2 f) xs 0).1.isSome (JSArray.some g ys) := by
  rw [search_some]
  exact (values.zipIdx 0).any _ _ (fun _ _ h => call2_erases function h.1 (congrArg Float.Model.ofNat h.2))

theorem listEvery_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number .bool)) interp}
    {g : (Core.Ty.fn a (.fn .number .bool)).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number .bool)) f g) (values : Erases (.list a) xs ys) :
    Erases (interp := interp) .bool (search (fun x index => let (value, safe) := call2 f x index; (!value, safe)) xs 0).1.isNone
      (JSArray.every g ys) := by
  rw [search_every]
  exact (values.zipIdx 0).all _ _ (fun _ _ h => call2_erases function h.1 (congrArg Float.Model.ofNat h.2))

theorem listFind_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number .bool)) interp}
    {g : (Core.Ty.fn a (.fn .number .bool)).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number .bool)) f g) (values : Erases (.list a) xs ys) :
    Erases (.option a) ((search (call2 f) xs 0).1.map Prod.snd) (JSArray.find g ys) := by
  rw [search_find]
  exact ((values.zipIdx 0).find? _ _ (fun _ _ h => call2_erases function h.1 (congrArg Float.Model.ofNat h.2))).map
    Prod.fst Prod.fst (fun _ _ h => h.1)

theorem listFindIndex_erases {interp : Named.Interp} {f : Model (.fn a (.fn .number .bool)) interp}
    {g : (Core.Ty.fn a (.fn .number .bool)).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)}
    (function : Erases (.fn a (.fn .number .bool)) f g) (values : Erases (.list a) xs ys) :
    Erases (interp := interp) .number (((search (call2 f) xs 0).1.map (fun result => Float.Model.ofNat result.1)).getD
      (Float.Model.ofInt (-1))) (JSArray.findIndex g ys) := by
  rw [search_findIndex]
  have found := (values.zipIdx 0).findIdx? _ _ (fun _ _ h => call2_erases function h.1 (congrArg Float.Model.ofNat h.2))
  change Float.Model.ofInt (((_ : Option Nat).map Int.ofNat).getD (-1)) = _
  exact congrArg (fun index : Option Nat => Float.Model.ofInt ((index.map Int.ofNat).getD (-1))) found

theorem each_erases {interp : Named.Interp}
    {f : Model (.fn a (.fn s (.step s r))) interp} {g : (Core.Ty.fn a (.fn s (.step s r))).denote interp}
    {xs : List (Model a interp)} {ys : List (a.denote interp)} {initial : Model s interp} {native : s.denote interp}
    (function : Erases (.fn a (.fn s (.step s r))) f g) (values : Erases (.list a) xs ys)
    (start : Erases s initial native) :
    Erases (.exit s r) (each (call2 f) xs initial).1 (Loop.each ys native g) := by
  induction values generalizing initial native with
  | nil => exact start
  | @cons x y xs ys head tail ih =>
    have step := call2_erases function head start
    cases hx : (call2 f x initial).1 <;> cases hy : g y native
    all_goals simp only [hx, hy, Erases] at step
    · simpa only [each, Loop.each, hx, hy] using ih step
    · simpa only [each, Loop.each, hx, hy, Erases] using step
    · simpa only [each, Loop.each, hx, hy, Erases] using step

end Ariadne.Shallow.Safety

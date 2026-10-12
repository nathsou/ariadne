import Ariadne.Shallow.Prelude.Loop
import Ariadne.Shallow.Prelude.Map
import Ariadne.Shallow.Prelude.Set
namespace Ariadne.Shallow

theorem Loop.each_append (xs ys : List α) (init : σ) (body : α → σ → Step σ τ)
    (noBreak : ∀ x ∈ xs, ∀ s s', body x s ≠ .stop s') :
    each (xs ++ ys) init body =
      match each xs init body with
      | .done s => each ys s body
      | .ret value => .ret value := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, each]
    cases h : body x init with
    | next s => exact ih s (fun y hy => noBreak y (List.mem_cons_of_mem x hy))
    | stop s => exact False.elim (noBreak x (by simp) init s h)
    | ret value => rfl

theorem Loop.range_invariant (start count : Nat) (init : σ) (body : Nat → σ → Step σ τ)
    (I : σ → Prop) (Q : τ → Prop) (initial : I init)
    (step : ∀ i, start ≤ i → i < start + count → ∀ s, I s → match body i s with
      | .next s | .stop s => I s
      | .ret v => Q v) :
    match range start count init body with
    | .done s => I s
    | .ret v => Q v := by
  apply each_invariant I Q initial
  intro i hi
  simp only [List.mem_range'] at hi
  rcases hi with ⟨j, hj, rfl⟩
  exact step _ (by omega) (by omega)

theorem Loop.range_foldl (start count : Nat) (init : σ) (body : Nat → σ → σ) :
    range (τ := τ) start count init (fun i s => .next (body i s)) =
      .done ((List.range' start count).foldl (fun s i => body i s) init) :=
  each_foldl _ _ _

theorem JSMap.keys_delete [BEq κ] (m : JSMap κ υ) (key : κ) :
    (m.delete key).keys = m.keys.filter (fun k => !(k == key)) := by
  simp only [delete, keys, MapEntries.delete, List.filter_map, Function.comp_def]

def JSMap.foldl [BEq κ] (f : α → κ → υ → α) (initial : α) (m : JSMap κ υ) : α :=
  m.entries.foldl (fun acc (key, value) => f acc key value) initial

theorem JSMap.foldl_entries [BEq κ] (f : α → κ → υ → α) (initial : α) (m : JSMap κ υ) :
    m.foldl f initial = m.entries.foldl (fun acc (key, value) => f acc key value) initial := rfl

theorem JSSet.LookupEq.refl [BEq κ] (s : JSSet κ) : LookupEq s s := fun _ => rfl
theorem JSSet.LookupEq.symm [BEq κ] {s t : JSSet κ} (eq : LookupEq s t) : LookupEq t s := fun k => (eq k).symm
theorem JSSet.LookupEq.trans [BEq κ] {s t u : JSSet κ} (st : LookupEq s t) (tu : LookupEq t u) :
    LookupEq s u := fun k => (st k).trans (tu k)
theorem JSSet.LookupEq.add [BEq κ] [EquivBEq κ] {s t : JSSet κ} (eq : LookupEq s t) (key : κ) :
    LookupEq (s.add key) (t.add key) := by intro query; simp only [has_add, eq query]
theorem JSSet.LookupEq.delete [BEq κ] [EquivBEq κ] {s t : JSSet κ} (eq : LookupEq s t) (key : κ) :
    LookupEq (s.delete key) (t.delete key) := by intro query; simp only [has_delete, eq query]

end Ariadne.Shallow

import Ariadne.Properties

namespace Ariadne

/-- When callback results are a pure function of elements, the modeled Array.map
returns exactly List.map. Callback allocation and unrelated effects may change the heap. -/
theorem traverse_map_eq_list_map (p : Program) (callback : Value) (f : Value → Value)
    (cost : Nat) (invariant : State → Prop) (domain : Value → Prop)
    (callbackSpec : ∀ fuel state value index, invariant state → domain value → cost ≤ fuel →
      ∃ after, apply p fuel state callback [value, .number (Float.Model.ofNat index)] =
        .ok (f value, after) ∧ invariant after)
    (values : List Value) (state : State) (index : Nat) (initial : invariant state)
    (elements : ∀ value, value ∈ values → domain value) :
    ∃ after, traverse p (values.length + cost + 1) state callback values index "map" =
      .ok (values.map f, after) ∧ invariant after := by
  induction values generalizing state index with
  | nil => exact ⟨state, rfl, initial⟩
  | cons value rest ih =>
    obtain ⟨called, hc, calledSafe⟩ := callbackSpec (rest.length + cost + 1) state value index initial
      (elements value (by simp)) (by omega)
    obtain ⟨after, ht, afterSafe⟩ := ih called (index + 1) calledSafe (fun value h => elements value (by simp [h]))
    refine ⟨after, ?_, afterSafe⟩
    have size : (value :: rest).length + cost + 1 = (rest.length + cost + 1) + 1 := by simp; omega
    rw [size, traverse, hc]
    simp [bind, pure, Except.bind, ht]
    rfl

/-- The explicit initial value makes modeled Array.reduce a total list fold,
provided every callback invocation meets its result and fuel contract. -/
theorem reduce_eq_foldl (p : Program) (callback : Value) (f : Value → Value → Value)
    (cost : Nat) (invariant : State → Prop) (domain accumulator : Value → Prop)
    (callbackSpec : ∀ fuel state acc value index,
      invariant state → accumulator acc → domain value → cost ≤ fuel →
      ∃ after, apply p fuel state callback [acc, value, .number (Float.Model.ofNat index)] =
        .ok (f acc value, after) ∧ invariant after ∧ accumulator (f acc value))
    (values : List Value) (state : State) (acc : Value) (index : Nat) (initial : invariant state)
    (accValid : accumulator acc) (elements : ∀ value, value ∈ values → domain value) :
    ∃ after, reduce p (values.length + cost + 1) state callback values acc index =
      .ok (values.foldl f acc, after) ∧ invariant after := by
  induction values generalizing state acc index with
  | nil => exact ⟨state, rfl, initial⟩
  | cons value rest ih =>
    obtain ⟨called, hc, calledSafe, nextValid⟩ := callbackSpec (rest.length + cost + 1) state acc value index
      initial accValid (elements value (by simp)) (by omega)
    obtain ⟨after, ht, afterSafe⟩ := ih called (f acc value) (index + 1) calledSafe nextValid
      (fun value h => elements value (by simp [h]))
    refine ⟨after, ?_, afterSafe⟩
    have size : (value :: rest).length + cost + 1 = (rest.length + cost + 1) + 1 := by simp; omega
    rw [size, reduce, hc]
    simpa [bind, pure, Except.bind] using ht

end Ariadne

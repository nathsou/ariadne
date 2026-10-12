import Ariadne.Shallow.Represents
import Ariadne.Shallow.Prelude.Array
import Ariadne.Semantics

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Reading a list element borrows a sub-footprint; it does not acquire the
array's owned footprint or permit independent mutation of that element. -/
theorem elements_get {element : DataRelation Value α} {heap : Heap}
    {values : List Value} {natives : List α} {footprint : Footprint}
    (input : Elements element heap values natives footprint) (index : Nat) :
    ∃ borrowed, borrowed ⊆ footprint ∧
      element.option.Holds heap (values[index]?.getD .undefined) natives[index]? borrowed := by
  induction input generalizing index with
  | nil => exact ⟨[], by simp, rfl, rfl⟩
  | @cons value native head values natives tail hv ht separate ih =>
    cases index with
    | zero => exact ⟨head, by simp, hv⟩
    | succ index =>
      rcases ih index with ⟨borrowed, subset, related⟩
      exact ⟨borrowed, fun _ member => List.mem_append_right _ (subset member), related⟩

theorem array_contents {element : DataRelation Value α} {heap : Heap} {value : Value}
    {natives : List α} {footprint : Footprint}
    (input : element.array.Holds heap value natives footprint) :
    ∃ address values children, value = .ref address ∧ heap[address]? = some (.array values) ∧
      Elements element heap values natives children ∧ address ∉ children ∧ footprint = address :: children := by
  rcases input with ⟨_, address, object, children, hv, lookup, contents, fresh, eq⟩
  rcases contents with ⟨values, project, related⟩
  cases object
  all_goals try contradiction
  case array actual =>
    cases project
    exact ⟨address, values, children, hv, lookup, related, fresh, eq⟩

theorem array_length {element : DataRelation Value α} {state : State} {value : Value}
    {natives : List α} {footprint : Footprint}
    (input : element.array.Holds state.heap value natives footprint) :
    readMember state value "length" = .ok (.number (Float.Model.ofNat natives.length)) := by
  rcases array_contents input with ⟨address, values, children, rfl, lookup, related, _, _⟩
  simp [readMember, lookup, related.length, pure, Except.pure]

/-- Index coercion is shared with the operational primitive, including NaN,
infinity, fractional indices and both zeros. The result borrows from the input. -/
theorem array_get {element : DataRelation Value α} {state : State} {value : Value}
    {natives : List α} {footprint : Footprint}
    (input : element.array.Holds state.heap value natives footprint) (index : Float.Model) :
    ∃ result borrowed, readIndex state value (.number index) = .ok result ∧
      borrowed ⊆ footprint ∧ element.option.Holds state.heap result (JSArray.get natives index) borrowed := by
  rcases array_contents input with ⟨address, values, children, rfl, lookup, related, _, rfl⟩
  cases converted : indexOf (.number index) with
  | none =>
    refine ⟨.undefined, [], ?_, by simp, ?_⟩
    · simp [readIndex, converted, pure, Except.pure]
    · simp [JSArray.get, converted, DataRelation.option]
  | some i =>
    rcases elements_get related i with ⟨borrowed, subset, found⟩
    refine ⟨values[i]?.getD .undefined, borrowed, ?_, ?_, ?_⟩
    · simp [readIndex, converted, lookup, pure, Except.pure]
    · exact fun _ member => List.mem_cons_of_mem _ (subset member)
    · simpa only [JSArray.get, converted, Option.bind_some] using found

end Ariadne.Shallow.Adequacy

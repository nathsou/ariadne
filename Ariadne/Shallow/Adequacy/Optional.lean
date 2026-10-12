import Ariadne.Shallow.Adequacy.Array
import Ariadne.Shallow.Adequacy.Map

namespace Ariadne.Shallow.DataRelation

/-- A present undefined payload and an absent lookup have the same source
observation. Flattening retains the borrowed footprint. -/
theorem option_join {r : DataRelation Value α} {heap : Heap} {value : Value}
    {native : Option (Option α)} {footprint : Heap.Footprint}
    (related : r.option.option.Holds heap value native footprint) :
    r.option.Holds heap value native.join footprint := by
  cases native with
  | none => exact related
  | some inner => cases inner <;> exact related

theorem option_unit {heap : Heap} {value : Value} {native : Option Unit}
    {footprint : Heap.Footprint} (related : unit.option.Holds heap value native footprint) :
    unit.Holds heap value () footprint := by
  cases native with
  | none => exact related
  | some inner => cases inner; exact related

/-- Presence is an undefined test only when present payloads cannot themselves
represent undefined. Lookup normalization establishes this requirement. -/
theorem option_undefined_iff {r : DataRelation Value α} {heap : Heap} {value : Value}
    {native : Option α} {footprint : Heap.Footprint}
    (related : r.option.Holds heap value native footprint)
    (defined : ∀ {value native footprint}, r.Holds heap value native footprint → value ≠ .undefined) :
    value = .undefined ↔ native.isSome = false := by
  cases native with
  | none => exact ⟨fun _ => rfl, fun _ => related.1⟩
  | some inner => simp only [Option.isSome_some, Bool.true_eq_false, iff_false]; exact defined related

end Ariadne.Shallow.DataRelation

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

theorem array_get_optional {element : DataRelation Value α} {state : State} {value : Value}
    {natives : List (Option α)} {footprint : Footprint}
    (input : element.option.array.Holds state.heap value natives footprint) (index : Float.Model) :
    ∃ result borrowed, readIndex state value (.number index) = .ok result ∧
      borrowed ⊆ footprint ∧
      element.option.Holds state.heap result (JSArray.get natives index).join borrowed := by
  obtain ⟨result, borrowed, read, subset, related⟩ := array_get input index
  exact ⟨result, borrowed, read, subset, option_join related⟩

theorem map_get_optional [BEq κ] {key : DataRelation Value κ} {value : DataRelation Value υ}
    {state : State} {address : Nat} {native : JSMap κ (Option υ)} {footprint : Footprint}
    (input : (DataRelation.map key value.option).Holds state.heap (.ref address) native footprint)
    (program : Program) (query : κ) (sourceQuery : Value)
    (keys : ∀ {source native footprint}, key.Holds state.heap source native footprint →
      sameValueZero source sourceQuery = (native == query)) :
    ∃ result borrowed, Invokes program state (.method address "get") [sourceQuery] result state ∧
      borrowed ⊆ footprint ∧ value.option.Holds state.heap result (native.get query).join borrowed := by
  obtain ⟨result, borrowed, invoke, subset, related⟩ := map_get input program query sourceQuery keys
  exact ⟨result, borrowed, invoke, subset, option_join related⟩

end Ariadne.Shallow.Adequacy

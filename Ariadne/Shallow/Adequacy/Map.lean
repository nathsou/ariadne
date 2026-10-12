import Ariadne.Shallow.Represents
import Ariadne.SourceFrom

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Map lookup uses the source key equality at each visited entry. The key
correspondence premise is local to scalar keys, not a whole-program contract. -/
theorem entries_get [BEq κ] {key : DataRelation Value κ} {value : DataRelation Value υ}
    {heap : Heap} {entries : List (Value × Value)} {natives : List (κ × υ)} {footprint : Footprint}
    (input : Elements (key.product value) heap entries natives footprint) (query : κ) (sourceQuery : Value)
    (keys : ∀ {source native footprint}, key.Holds heap source native footprint →
      sameValueZero source sourceQuery = (native == query)) :
    ∃ borrowed, borrowed ⊆ footprint ∧
      value.option.Holds heap (mapGet entries sourceQuery) (MapEntries.get natives query) borrowed := by
  induction input with
  | nil => exact ⟨[], by simp, rfl, rfl⟩
  | @cons entry native head entries natives tail pair rest separate ih =>
    rcases entry with ⟨sourceKey, sourceValue⟩
    rcases native with ⟨nativeKey, nativeValue⟩
    rcases pair with ⟨fk, fv, hk, hv, _, rfl⟩
    have same := keys hk
    by_cases found : (nativeKey == query) = true
    · refine ⟨fv, by simp, ?_⟩
      simpa [mapGet, MapEntries.get, same, found, DataRelation.option] using hv
    · rcases ih with ⟨borrowed, subset, related⟩
      refine ⟨borrowed, fun _ member => List.mem_append_right _ (subset member), ?_⟩
      simpa [mapGet, MapEntries.get, same, found] using related

theorem map_contents [BEq κ] {key : DataRelation Value κ} {value : DataRelation Value υ}
    {heap : Heap} {source : Value} {native : JSMap κ υ} {footprint : Footprint}
    (input : (DataRelation.map key value).Holds heap source native footprint) :
    ∃ address entries children, source = .ref address ∧ heap[address]? = some (.map entries) ∧
      Elements (key.product value) heap entries native.entries children ∧
      address ∉ children ∧ footprint = address :: children := by
  rcases input with ⟨address, object, children, hv, lookup, contents, fresh, eq⟩
  rcases contents with ⟨entries, project, related⟩
  cases object
  all_goals try contradiction
  case map actual =>
    cases project
    exact ⟨address, entries, children, hv, lookup, related, fresh, eq⟩

theorem map_get [BEq κ] {key : DataRelation Value κ} {value : DataRelation Value υ}
    {state : State} {address : Nat} {native : JSMap κ υ} {footprint : Footprint}
    (input : (DataRelation.map key value).Holds state.heap (.ref address) native footprint)
    (program : Program) (query : κ) (sourceQuery : Value)
    (keys : ∀ {source native footprint}, key.Holds state.heap source native footprint →
      sameValueZero source sourceQuery = (native == query)) :
    ∃ result borrowed, Invokes program state (.method address "get") [sourceQuery] result state ∧
      borrowed ⊆ footprint ∧ value.option.Holds state.heap result (native.get query) borrowed := by
  rcases map_contents input with ⟨actual, entries, children, equal, lookup, related, _, rfl⟩
  cases equal
  rcases entries_get related query sourceQuery keys with ⟨borrowed, subset, found⟩
  refine ⟨mapGet entries sourceQuery, borrowed, ?_, ?_, found⟩
  · refine ⟨(by intro h; cases h), 1, ?_⟩
    simp [apply, lookup, pure, Except.pure]
  · exact fun _ member => List.mem_cons_of_mem _ (subset member)

/-- Canonical scalar codecs discharge the map key premise directly. -/
theorem int_key {heap : Heap} {source : Value} {native query : Int} {footprint : Footprint}
    (input : DataRelation.int.Holds heap source native footprint) :
    sameValueZero source (.bigint query) = (native == query) := by
  rcases input with ⟨rfl, _⟩
  rfl

theorem string_key {heap : Heap} {source : Value} {native query : JSString} {footprint : Footprint}
    (input : DataRelation.string.Holds heap source native footprint) :
    sameValueZero source (.string query) = (native == query) := by
  rcases input with ⟨rfl, _⟩
  rfl

theorem bool_key {heap : Heap} {source : Value} {native query : Bool} {footprint : Footprint}
    (input : DataRelation.bool.Holds heap source native footprint) :
    sameValueZero source (.boolean query) = (native == query) := by
  rcases input with ⟨rfl, _⟩
  rfl

theorem number_key {heap : Heap} {source : Value} {native query : Float.Model} {footprint : Footprint}
    (input : DataRelation.number.Holds heap source native footprint) :
    sameValueZero source (.number query) = NumberKey.equal native query := by
  rcases input with ⟨rfl, _⟩
  rfl

end Ariadne.Shallow.Adequacy

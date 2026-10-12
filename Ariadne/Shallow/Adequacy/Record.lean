import Ariadne.Shallow.Represents
import Ariadne.Semantics

namespace Ariadne.Shallow
open Heap
namespace DataRelation

/-- Change only the runtime view of a compositional relation. -/
def onRuntime (relation : DataRelation runtime native) (view : source → runtime) : DataRelation source native where
  Holds heap value native footprint := relation.Holds heap (view value) native footprint
  allocated := relation.allocated
  frame := relation.frame

/-- Records observe absent optional fields as undefined. Required fields can
continue to use `field`; class fields must be present to avoid method lookup. -/
def defaultField (name : String) (head : DataRelation Value α)
    (tail : DataRelation (List (String × Value)) β) : DataRelation (List (String × Value)) (α × β) :=
  (head.product tail).onRuntime (fun fields => ((fields.lookup name).getD .undefined, fields))

/-- A field projection borrows only the footprint of the selected value. -/
def ReadsField (layout : DataRelation (List (String × Value)) α) (name : String)
    (element : DataRelation Value β) (get : α → β) : Prop :=
  ∀ {heap fields native footprint}, layout.Holds heap fields native footprint →
    ∃ borrowed, borrowed ⊆ footprint ∧
      element.Holds heap ((fields.lookup name).getD .undefined) (get native) borrowed

theorem ReadsField.default_head (name : String) (head : DataRelation Value α)
    (tail : DataRelation (List (String × Value)) β) : ReadsField (defaultField name head tail) name head Prod.fst := by
  rintro heap fields native footprint ⟨left, right, hl, hr, separate, rfl⟩
  exact ⟨left, by simp, hl⟩

theorem ReadsField.required_head (name : String) (head : DataRelation Value α)
    (tail : DataRelation (List (String × Value)) β) : ReadsField (field name head tail) name head Prod.fst := by
  rintro heap fields native footprint ⟨value, lookup, left, right, hl, hr, separate, rfl⟩
  exact ⟨left, by simp, by simpa [lookup] using hl⟩

theorem ReadsField.default_tail {layout : DataRelation (List (String × Value)) α} {name : String}
    {element : DataRelation Value β} {get : α → β} (input : ReadsField layout name element get)
    (other : String) (head : DataRelation Value γ) :
    ReadsField (defaultField other head layout) name element (get ∘ Prod.snd) := by
  rintro heap fields native footprint ⟨left, right, hl, hr, separate, rfl⟩
  obtain ⟨borrowed, subset, related⟩ := input hr
  exact ⟨borrowed, fun _ member => List.mem_append_right _ (subset member), related⟩

theorem ReadsField.required_tail {layout : DataRelation (List (String × Value)) α} {name : String}
    {element : DataRelation Value β} {get : α → β} (input : ReadsField layout name element get)
    (other : String) (head : DataRelation Value γ) :
    ReadsField (field other head layout) name element (get ∘ Prod.snd) := by
  rintro heap fields native footprint ⟨value, lookup, left, right, hl, hr, separate, rfl⟩
  obtain ⟨borrowed, subset, related⟩ := input hr
  exact ⟨borrowed, fun _ member => List.mem_append_right _ (subset member), related⟩

/-- Replacing an owned object's root preserves its disjoint child observations
and every framed object outside that root. -/
theorem reference_write (contents : DataRelation Object α) (state : State) (address : Nat)
    (object : Object) (native : α) (children : Footprint)
    (allocated : address < state.heap.length) (input : contents.Holds state.heap object native children)
    (separate : address ∉ children) :
    ∃ after, state.write address object = .ok after ∧
      contents.reference.Holds after.heap (.ref address) native (address :: children) ∧
      Modifies [address] state.heap after.heap := by
  let after := { state with heap := state.heap.set address object }
  have written : state.write address object = .ok after := by simp [State.write, allocated, after]
  refine ⟨after, written, ?_, State.write_modifies written⟩
  refine ⟨address, object, children, rfl, ?_, ?_, separate, rfl⟩
  · simp [after, allocated]
  · exact contents.frame input (agreesOn_set state.heap children address object separate)

end DataRelation
namespace Adequacy
open DataRelation

theorem record_contents {layout : DataRelation (List (String × Value)) α} {heap : Heap} {value : Value}
    {native : α} {footprint : Footprint} (input : layout.record.Holds heap value native footprint) :
    ∃ address fields children, value = .ref address ∧ heap[address]? = some (.record fields) ∧
      layout.Holds heap fields native children ∧ address ∉ children ∧ footprint = address :: children := by
  rcases input with ⟨address, object, children, hv, lookup, contents, fresh, eq⟩
  rcases contents with ⟨fields, project, related⟩
  cases object
  all_goals try contradiction
  case record actual =>
    cases project
    exact ⟨address, fields, children, hv, lookup, related, fresh, eq⟩

theorem record_get {layout : DataRelation (List (String × Value)) α} {element : DataRelation Value β}
    {state : State} {value : Value} {native : α} {footprint : Footprint} {name : String} {get : α → β}
    (input : layout.record.Holds state.heap value native footprint) (field : ReadsField layout name element get) :
    ∃ result borrowed, readMember state value name = .ok result ∧ borrowed ⊆ footprint ∧
      element.Holds state.heap result (get native) borrowed := by
  rcases record_contents input with ⟨address, fields, children, rfl, lookup, related, fresh, rfl⟩
  obtain ⟨borrowed, subset, result⟩ := field related
  refine ⟨(fields.lookup name).getD .undefined, borrowed, ?_, ?_, result⟩
  · simp [readMember, lookup, pure, Except.pure]
  · exact fun _ member => List.mem_cons_of_mem _ (subset member)

/-- Both physical record layouts implement the same optional-field observation. -/
theorem optional_field_missing_or_undefined (element : DataRelation Value α)
    (heap : Heap) (fields : List (String × Value)) (name : String)
    (missing : fields.lookup name = none ∨ fields.lookup name = some .undefined) :
    (defaultField name element.option fieldsNil).Holds heap fields (none, ()) [] := by
  refine ⟨[], [], ?_, ⟨True.intro, rfl⟩, ?_, rfl⟩
  · rcases missing with missing | missing <;> exact ⟨by simp [missing], rfl⟩
  · simp [Disjoint]

end Adequacy
end Ariadne.Shallow

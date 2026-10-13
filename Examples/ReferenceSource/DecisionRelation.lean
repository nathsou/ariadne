import Examples.ReferenceSource.Decision
import Ariadne.Shallow.Adequacy.WPRecord

/-!
# The candidate layout is the generated representation

`layout` is the data relation the extractor's representation combinators give
`Candidate`: a union of two records, each selected by its literal `kind` field.
It holds exactly when the concrete `CandidateAt` used by the source proofs does,
so `choose`'s source theorem also holds for inputs and results stated with the
generated relations.
-/

namespace Examples.ReferenceSource.Decision
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_decision.Shallow
open Heap DataRelation

def layout : DataRelation Value Candidate :=
  (DataRelation.sum
    (record (field "kind" (literal (.string validKind)) (field "version" int53 (field "id" string fieldsNil))))
    (record (field "kind" (literal (.string rejectedKind)) (field "reason" string fieldsNil)))).comap
    NativeDestruct.«Candidate»

def validFields :=
  FieldsCodec.cons "kind" (ScalarCodec.literal (.string validKind))
    (FieldsCodec.cons "version" ScalarCodec.int53 (FieldsCodec.cons "id" ScalarCodec.string FieldsCodec.nil))

def rejectedFields :=
  FieldsCodec.cons "kind" (ScalarCodec.literal (.string rejectedKind))
    (FieldsCodec.cons "reason" ScalarCodec.string FieldsCodec.nil)

theorem layout_iff {heap : Heap} {value : Value} {c : Candidate} {footprint : Footprint} :
    layout.Holds heap value c footprint ↔ ∃ a, value = .ref a ∧ CandidateAt heap a c ∧ footprint = [a] := by
  cases c with
  | valid v =>
    show (record validFields.relation).Holds heap value (NativeDestruct.«Candidate#left» v) footprint ↔ _
    rw [record_codec_iff]
    constructor
    · rintro ⟨a, fields, rfl, lookup, ⟨⟨-, kind⟩, ⟨range, version⟩, ⟨-, id⟩, -⟩, rfl⟩
      exact ⟨a, rfl, ⟨fields, lookup, kind, version, id, range⟩, rfl⟩
    · rintro ⟨a, rfl, ⟨fields, lookup, kind, version, id, range⟩, rfl⟩
      exact ⟨a, fields, rfl, lookup, ⟨⟨trivial, kind⟩, ⟨range, version⟩, ⟨trivial, id⟩, trivial⟩, rfl⟩
  | rejected r =>
    show (record rejectedFields.relation).Holds heap value (NativeDestruct.«Candidate#right» r) footprint ↔ _
    rw [record_codec_iff]
    constructor
    · rintro ⟨a, fields, rfl, lookup, ⟨⟨-, kind⟩, ⟨-, reason⟩, -⟩, rfl⟩
      exact ⟨a, rfl, ⟨fields, lookup, kind, reason⟩, rfl⟩
    · rintro ⟨a, rfl, ⟨fields, lookup, kind, reason⟩, rfl⟩
      exact ⟨a, fields, rfl, lookup, ⟨⟨trivial, kind⟩, ⟨trivial, reason⟩, trivial⟩, rfl⟩

/-- Array elements under the generated relation are references to candidate records. -/
theorem elements_refs {heap : Heap} {values : List Value} {natives : List Candidate} {footprint : Footprint}
    (h : Elements layout heap values natives footprint) :
    ∃ refs, values = refs.map .ref ∧ Elementwise (CandidateAt heap) refs natives := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons head _ _ ih =>
    obtain ⟨a, rfl, at_, -⟩ := layout_iff.mp head
    obtain ⟨refs, rfl, elements⟩ := ih
    exact ⟨a :: refs, rfl, .cons at_ elements⟩

theorem array_refs {heap : Heap} {value : Value} {natives : List Candidate} {footprint : Footprint}
    (h : (array layout).Holds heap value natives footprint) :
    ∃ address refs, value = .ref address ∧ heap[address]? = some (.array (refs.map .ref)) ∧
      Elementwise (CandidateAt heap) refs natives := by
  obtain ⟨-, address, object, children, rfl, lookup, ⟨values, project, related⟩, _, rfl⟩ := h
  have hobj : object = .array values := by cases object <;> simp_all
  subst hobj
  obtain ⟨refs, rfl, elements⟩ := elements_refs related
  exact ⟨address, refs, rfl, lookup, elements⟩

theorem BestAt.represents {heap : Heap} {refs : List Nat} {value : Value} {best : Option Candidate}
    (h : BestAt heap refs value best) : Represents layout.option heap value best := by
  cases best with
  | none => exact ⟨[], h, rfl⟩
  | some c =>
    obtain ⟨a, rfl, _, at_, _⟩ := h
    exact ⟨[a], layout_iff.mpr ⟨a, rfl, at_, rfl⟩⟩

/-- `choose`, stated with the generated relations: for every candidate array the
source run's result represents the emitted `choose` in the input heap. -/
theorem choose_represents (before : State) (value : Value) (natives : List Candidate) (footprint : Footprint)
    (floor : Int) (floorRange : Int53.InRange floor)
    (input : (array layout).Holds before.heap value natives footprint) :
    ∃ result after, SourceInvokes Extracted_reference_decision.source before (.function "choose")
      [value, .number (Float.Model.ofInt floor)] result after ∧
      Represents layout.option before.heap result («choose» natives floor) := by
  obtain ⟨address, refs, rfl, arrayAt, elements⟩ := array_refs input
  obtain ⟨result, after, run, best⟩ :=
    choose_spec_source before address refs natives floor floorRange arrayAt elements
  exact ⟨result, after, run, best.represents⟩

end Examples.ReferenceSource.Decision

import Ariadne.Shallow.Adequacy.WPData
import Ariadne.Shallow.Adequacy.ClassConstruction
import Ariadne.Shallow.Adequacy.Record

/-!
Weakest-precondition rules for record literals, and codecs for records whose
fields are scalars. A codec states a record relation as plain lookups on the
heap object's fields, so generated proofs read inputs and build results by
rewriting rather than by unfolding the relation combinators.
-/

namespace Ariadne

def WPFields (program : Program) (state : State) (fields : List (String × Expr))
    (acc : List (String × Value)) (post : List (String × Value) → State → Prop) : Prop :=
  ∃ values after, EvaluatesFields program state fields acc values after ∧ post values after

theorem WPFields.nil {program : Program} {state : State} {acc : List (String × Value)}
    {post : List (String × Value) → State → Prop} (h : post acc state) : WPFields program state [] acc post :=
  ⟨acc, state, EvaluatesFields.nil program state acc, h⟩

theorem WPFields.cons {program : Program} {state : State} {acc : List (String × Value)}
    {post : List (String × Value) → State → Prop} {name : String} {expression : Expr}
    {rest : List (String × Expr)} (named : name ≠ "")
    (h : WPE program state expression (fun v middle =>
      WPFields program middle rest (fieldSet acc name v) post)) :
    WPFields program state ((name, expression) :: rest) acc post := by
  unfold WPE at h
  obtain ⟨v, middle, e, values, after, es, q⟩ := h
  exact ⟨values, after, EvaluatesFields.cons e es named, q⟩

theorem WPE.record {program : Program} {state : State} {post : Value → State → Prop}
    {fields : List (String × Expr)} {span : Span}
    (h : WPFields program state fields [] (fun values after =>
      post (.ref after.heap.length) (after.alloc (.record values)).2)) :
    WPE program state (.record fields span) post := by
  unfold WPE
  obtain ⟨values, after, e, q⟩ := h
  obtain ⟨n, hn⟩ := e.eventually
  refine ⟨_, _, ⟨(by intro h; cases h), n + 1, ?_⟩, q⟩
  simp [evalExpr, hn n (Nat.le_refl _), State.alloc, bind, Except.bind, pure, Except.pure]

attribute [irreducible] WPFields

namespace Shallow.Adequacy
open Shallow DataRelation

/-- Absent scalars read as `undefined`. -/
def ScalarCodec.option (codec : ScalarCodec κ) : ScalarCodec (Option κ) where
  encode o := (o.map codec.encode).getD .undefined
  valid o := ∀ x, o = some x → codec.valid x
  relation := codec.relation.option
  holds := by
    intro heap value native footprint
    cases native with
    | none => simp [DataRelation.option]
    | some x => simpa [DataRelation.option] using codec.holds

/-- A field of a single literal value, such as a union tag. -/
def ScalarCodec.literal (expected : Value) : ScalarCodec Unit where
  encode _ := expected
  valid _ := True
  relation := DataRelation.literal expected
  holds := by intros; simp [DataRelation.literal, DataRelation.scalar]

/-- Record fields of scalars, as lookups on the field list. -/
structure FieldsCodec (α : Type) where
  relation : DataRelation (List (String × Value)) α
  Reads : List (String × Value) → α → Prop
  holds : ∀ {heap fields native footprint}, relation.Holds heap fields native footprint ↔
    Reads fields native ∧ footprint = []

def FieldsCodec.nil : FieldsCodec Unit where
  relation := fieldsNil
  Reads _ _ := True
  holds := by intros; simp [fieldsNil, DataRelation.scalar]

/-- A required field: present, holding the encoded scalar. -/
def FieldsCodec.cons (name : String) (codec : ScalarCodec α) (tail : FieldsCodec β) : FieldsCodec (α × β) where
  relation := field name codec.relation tail.relation
  Reads fields native := (codec.valid native.1 ∧ fields.lookup name = some (codec.encode native.1)) ∧
    tail.Reads fields native.2
  holds := by
    intro heap fields native footprint
    constructor
    · rintro ⟨value, lookup, fl, fr, hl, hr, _, rfl⟩
      obtain ⟨⟨valid, rfl⟩, rfl⟩ := codec.holds.mp hl
      obtain ⟨reads, rfl⟩ := tail.holds.mp hr
      exact ⟨⟨⟨valid, lookup⟩, reads⟩, rfl⟩
    · rintro ⟨⟨⟨valid, lookup⟩, reads⟩, rfl⟩
      exact ⟨_, lookup, [], [], codec.holds.mpr ⟨⟨valid, rfl⟩, rfl⟩, tail.holds.mpr ⟨reads, rfl⟩,
        by simp [Heap.Disjoint], rfl⟩

/-- A field that reads as `undefined` when absent. -/
def FieldsCodec.default (name : String) (codec : ScalarCodec α) (tail : FieldsCodec β) : FieldsCodec (α × β) where
  relation := defaultField name codec.relation tail.relation
  Reads fields native := (codec.valid native.1 ∧ (fields.lookup name).getD .undefined = codec.encode native.1) ∧
    tail.Reads fields native.2
  holds := by
    intro heap fields native footprint
    constructor
    · rintro ⟨fl, fr, hl, hr, _, rfl⟩
      obtain ⟨⟨valid, read⟩, rfl⟩ := codec.holds.mp hl
      obtain ⟨reads, rfl⟩ := tail.holds.mp hr
      exact ⟨⟨⟨valid, read⟩, reads⟩, rfl⟩
    · rintro ⟨⟨⟨valid, read⟩, reads⟩, rfl⟩
      exact ⟨[], [], codec.holds.mpr ⟨⟨valid, read⟩, rfl⟩, tail.holds.mpr ⟨reads, rfl⟩,
        by simp [Heap.Disjoint], rfl⟩

/-- A record of scalars is one heap object whose fields read as the encoded natives. -/
theorem record_codec_iff (codec : FieldsCodec α) {heap : Heap} {value : Value} {native : α}
    {footprint : Heap.Footprint} :
    (record codec.relation).Holds heap value native footprint ↔
      ∃ a fields, value = .ref a ∧ heap[a]? = some (.record fields) ∧ codec.Reads fields native ∧
        footprint = [a] := by
  constructor
  · rintro ⟨a, object, children, rfl, lookup, ⟨fields, project, related⟩, _, rfl⟩
    have hobj : object = .record fields := by cases object <;> simp_all
    subst hobj
    obtain ⟨reads, rfl⟩ := codec.holds.mp related
    exact ⟨a, fields, rfl, lookup, reads, rfl⟩
  · rintro ⟨a, fields, rfl, lookup, reads, rfl⟩
    exact ⟨a, _, [], rfl, lookup, ⟨fields, rfl, codec.holds.mpr ⟨reads, rfl⟩⟩, by simp, rfl⟩

/-- The same, through the native record's destructor. -/
theorem record_comap_iff (codec : FieldsCodec α) (destruct : β → α) {heap : Heap} {value : Value}
    {native : β} {footprint : Heap.Footprint} :
    ((record codec.relation).comap destruct).Holds heap value native footprint ↔
      ∃ a fields, value = .ref a ∧ heap[a]? = some (.record fields) ∧ codec.Reads fields (destruct native) ∧
        footprint = [a] :=
  record_codec_iff codec

theorem record_represents (codec : FieldsCodec α) (destruct : β → α) {heap : Heap} {native : β} {a : Nat}
    {fields : List (String × Value)} (lookup : heap[a]? = some (.record fields))
    (reads : codec.Reads fields (destruct native)) :
    Represents ((record codec.relation).comap destruct) heap (.ref a) native :=
  ⟨_, (record_comap_iff codec destruct).mpr ⟨a, fields, rfl, lookup, reads, rfl⟩⟩

end Shallow.Adequacy

end Ariadne

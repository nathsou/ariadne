import Ariadne.Shallow.Adequacy.Record
import Ariadne.StatementConvergence

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Assignment observes the new value even when source records contain repeated keys. -/
theorem fieldSet_lookup_self (fields : List (String × Value)) (key : String) (value : Value) :
    (fieldSet fields key value).lookup key = some value := by
  induction fields with
  | nil => simp [fieldSet]
  | cons pair rest ih =>
    rcases pair with ⟨name, old⟩
    by_cases same : name = key
    · subst name
      simp [fieldSet]
    · have forward : (name == key) = false := beq_eq_false_iff_ne.mpr same
      have backward : (key == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      unfold fieldSet
      simp only [List.any_cons, forward, Bool.false_or]
      unfold fieldSet at ih
      split <;> rename_i present
      · simp only [present] at ih
        simpa only [List.map_cons, forward, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, backward] using ih
      · simp only [present] at ih
        simpa only [List.cons_append, List.lookup_cons, backward, Bool.false_eq_true, ↓reduceIte] using ih

/-- Every other field keeps its runtime value and identity. -/
theorem fieldSet_lookup_other (fields : List (String × Value)) (key query : String) (value : Value)
    (different : query ≠ key) :
    (fieldSet fields key value).lookup query = fields.lookup query := by
  induction fields with
  | nil => simp [fieldSet, different]
  | cons pair rest ih =>
    rcases pair with ⟨name, old⟩
    unfold fieldSet
    by_cases same : name = key
    · subst name
      simp only [List.any_cons, beq_self_eq_true, Bool.true_or, ↓reduceIte, List.map_cons]
      simp only [List.lookup_cons, show (query == key) = false from beq_eq_false_iff_ne.mpr different]
      have mapped : ∀ entries : List (String × Value),
          (entries.map (fun (k, v) => (k, if k == key then value else v))).lookup query = entries.lookup query := by
        intro entries
        induction entries with
        | nil => rfl
        | cons pair rest ih =>
          rcases pair with ⟨name, old⟩
          by_cases found : query = name
          · subst name
            simp [different]
          · have skip : (query == name) = false := beq_eq_false_iff_ne.mpr found
            simpa only [List.map_cons, List.lookup_cons, skip] using ih
      exact mapped rest
    · have forward : (name == key) = false := beq_eq_false_iff_ne.mpr same
      simp only [List.any_cons, forward, Bool.false_or]
      unfold fieldSet at ih
      split <;> rename_i present
      · simp only [present] at ih
        simp only [List.map_cons, forward, Bool.false_eq_true, ↓reduceIte, List.lookup_cons]
        split <;> simp_all
      · simp only [present] at ih
        simp only [List.cons_append, List.lookup_cons]
        split <;> simp_all

/-- The rest of a record's layout does not observe the field being updated. -/
def IgnoresField (layout : DataRelation (List (String × Value)) α) (name : String) : Prop :=
  ∀ {heap fields native footprint} (value : Value), layout.Holds heap fields native footprint →
    layout.Holds heap (fieldSet fields name value) native footprint

theorem IgnoresField.nil (name : String) : IgnoresField fieldsNil name := by
  intro heap fields native footprint value related
  exact related

theorem IgnoresField.required {layout : DataRelation (List (String × Value)) β} {name other : String}
    (head : DataRelation Value α) (tail : IgnoresField layout name) (different : other ≠ name) :
    IgnoresField (DataRelation.field other head layout) name := by
  intro heap fields native footprint value related
  obtain ⟨old, lookup, left, right, first, rest, separate, rfl⟩ := related
  exact ⟨old, (fieldSet_lookup_other fields name other value different).trans lookup,
    left, right, first, tail value rest, separate, rfl⟩

theorem IgnoresField.default {layout : DataRelation (List (String × Value)) β} {name other : String}
    (head : DataRelation Value α) (tail : IgnoresField layout name) (different : other ≠ name) :
    IgnoresField (DataRelation.defaultField other head layout) name := by
  intro heap fields native footprint value related
  obtain ⟨left, right, first, rest, separate, rfl⟩ := related
  refine ⟨left, right, ?_, tail value rest, separate, rfl⟩
  simpa only [fieldSet_lookup_other fields name other value different] using first

/-- A scalar field write changes only the record root. The unchanged layout
can contain reference fields; those children are framed, rather than copied. -/
theorem record_scalar_set {codec : Value → α → Prop} {tail : DataRelation (List (String × Value)) β}
    {state : State} {address : Nat} {old updated : α} {rest : β} {owned : Footprint}
    (name : String) (value : Value)
    (input : (DataRelation.field name (DataRelation.scalar codec) tail).record.Holds
      state.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name) (encoded : codec value updated) :
    ∃ fields after,
      state.heap[address]? = some (.record fields) ∧
      state.write address (.record (fieldSet fields name value)) = .ok after ∧
      (DataRelation.field name (DataRelation.scalar codec) tail).record.Holds
        after.heap (.ref address) (updated, rest) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨root, fields, children, same, lookup, related, fresh, footprint⟩ := record_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  obtain ⟨oldValue, oldLookup, left, right, oldRelated, tailRelated, _, childrenEq⟩ := related
  obtain ⟨_, rfl⟩ := oldRelated
  simp only [List.nil_append] at childrenEq
  subst children
  let after := {state with heap := state.heap.set address (.record (fieldSet fields name value))}
  have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have written : state.write address (.record (fieldSet fields name value)) = .ok after := by
    simp [State.write, allocated, after]
  have framed := tail.frame (independent value tailRelated)
    (agreesOn_set state.heap right address (.record (fieldSet fields name value)) fresh)
  refine ⟨fields, after, lookup, written, ?_, State.write_modifies written⟩
  rw [footprint]
  refine ⟨address, .record (fieldSet fields name value), right, rfl, ?_, ?_, fresh, rfl⟩
  · simp [after, allocated]
  · exact ⟨fieldSet fields name value, rfl, value, fieldSet_lookup_self fields name value,
      [], right, ⟨encoded, rfl⟩, framed, (by simp [Disjoint]), rfl⟩

/-- Compose field framing with the original compound-update statement.
Premises describe subexpressions and a primitive operator, not whole execution. -/
theorem record_scalar_update {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {program : Program} {state : State}
    {address : Nat} {old updated : α} {rest : β} {owned : Footprint}
    (name op : String) (receiver rhs : Expr) (delta value : Value) (span : Span)
    (input : (DataRelation.field name (DataRelation.scalar codec) tail).record.Holds
      state.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name)
    (receiverEval : Evaluates program state receiver (.ref address) state)
    (operandEval : Evaluates program state rhs delta state)
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ after,
      ExecutesStatement program state (.update (.member receiver name span) op rhs span) {state := after} ∧
      (DataRelation.field name (DataRelation.scalar codec) tail).record.Holds
        after.heap (.ref address) (updated, rest) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨before, _, read, _, represented⟩ := record_get input
    (ReadsField.required_head name (DataRelation.scalar codec) tail)
  obtain ⟨fields, after, lookup, written, related, modifies⟩ := record_scalar_set name value input independent encoded
  exact ⟨after, ExecutesStatement.update (UpdatesTarget.record receiverEval read operandEval
    (operation before represented.1) lookup written span) span, related, modifies⟩

end Ariadne.Shallow.Adequacy

import Ariadne.Heap
import Ariadne.Shallow.Core
import Ariadne.Shallow.Prelude.Int53

namespace Ariadne.Shallow
open Heap

/-- A heap-dependent data relation with a finite read footprint. The two laws
make framing compositional; neither law asserts execution correctness. Runtime
layouts are explicit because Core pairs alone do not distinguish source tuples
from records, and a named shape does not retain source field names. -/
structure DataRelation (runtime native : Type) where
  Holds : Heap → runtime → native → Footprint → Prop
  allocated : ∀ {heap value native footprint}, Holds heap value native footprint → Allocated heap footprint
  frame : ∀ {before after value native footprint}, Holds before value native footprint →
    AgreesOn footprint before after → Holds after value native footprint

abbrev Represents (layout : DataRelation Value α) (heap : Heap) (value : Value) (native : α) : Prop :=
  ∃ footprint, layout.Holds heap value native footprint

namespace DataRelation

def scalar (relation : runtime → native → Prop) : DataRelation runtime native where
  Holds _ value native footprint := relation value native ∧ footprint = []
  allocated := by rintro _ _ _ _ ⟨_, rfl⟩; simp [Allocated]
  frame := by intros; assumption

def comap (r : DataRelation runtime α) (f : β → α) : DataRelation runtime β where
  Holds heap value native footprint := r.Holds heap value (f native) footprint
  allocated := r.allocated
  frame := r.frame

def refine (r : DataRelation runtime α) (valid : α → Prop) : DataRelation runtime α where
  Holds heap value native footprint := valid native ∧ r.Holds heap value native footprint
  allocated := fun h => r.allocated h.2
  frame := fun h eq => ⟨h.1, r.frame h.2 eq⟩

def product (left : DataRelation ra α) (right : DataRelation rb β) : DataRelation (ra × rb) (α × β) where
  Holds heap value native footprint := ∃ fl fr,
    left.Holds heap value.1 native.1 fl ∧ right.Holds heap value.2 native.2 fr ∧
    Disjoint fl fr ∧ footprint = fl ++ fr
  allocated := by
    rintro heap value native _ ⟨fl, fr, hl, hr, _, rfl⟩ address member
    rcases List.mem_append.mp member with member | member
    · exact left.allocated hl address member
    · exact right.allocated hr address member
  frame := by
    rintro before after value native _ ⟨fl, fr, hl, hr, separate, rfl⟩ eq
    exact ⟨fl, fr, left.frame hl (eq.mono (by simp)),
      right.frame hr (eq.mono (by simp)), separate, rfl⟩

inductive Elements (r : DataRelation runtime native) (heap : Heap) :
    List runtime → List native → Footprint → Prop where
  | nil : Elements r heap [] [] []
  | cons : r.Holds heap value element head → Elements r heap values natives tail →
      Disjoint head tail → Elements r heap (value :: values) (element :: natives) (head ++ tail)

theorem Elements.allocated {r : DataRelation runtime native} {heap : Heap}
    {values : List runtime} {natives : List native} {footprint : Footprint}
    (h : Elements r heap values natives footprint) : Allocated heap footprint := by
  induction h with
  | nil => simp [Allocated]
  | cons head _ _ ih =>
    intro i member
    rcases List.mem_append.mp member with member | member
    · exact r.allocated head i member
    · exact ih i member

theorem Elements.frame {r : DataRelation runtime native} {before after : Heap}
    {values : List runtime} {natives : List native} {footprint : Footprint}
    (h : Elements r before values natives footprint) (eq : AgreesOn footprint before after) :
    Elements r after values natives footprint := by
  induction h with
  | nil => exact .nil
  | cons head _ separate ih =>
    exact .cons (r.frame head (eq.mono (by simp))) (ih (eq.mono (by simp))) separate

theorem Elements.length {r : DataRelation runtime native} {heap : Heap}
    {values : List runtime} {natives : List native} {footprint : Footprint}
    (h : Elements r heap values natives footprint) : values.length = natives.length := by
  induction h <;> simp_all

def sequence (r : DataRelation runtime native) : DataRelation (List runtime) (List native) where
  Holds := Elements r
  allocated := Elements.allocated
  frame := Elements.frame

/-- An owned object and the disjoint footprints of its contents. Requiring the
root to be fresh for its descendants excludes cyclic owned inputs. -/
def reference (contents : DataRelation Object α) : DataRelation Value α where
  Holds heap value native footprint := ∃ address object children,
    value = .ref address ∧ heap[address]? = some object ∧
    contents.Holds heap object native children ∧ address ∉ children ∧ footprint = address :: children
  allocated := by
    rintro heap value native _ ⟨address, object, children, _, lookup, related, _, rfl⟩ i member
    rcases List.mem_cons.mp member with rfl | member
    · exact (List.getElem?_eq_some_iff.mp lookup).choose
    · exact contents.allocated related i member
  frame := by
    rintro before after value native _ ⟨address, object, children, hv, lookup, related, fresh, rfl⟩ eq
    exact ⟨address, object, children, hv, (eq address (by simp)).symm.trans lookup,
      contents.frame related (eq.mono (by simp)), fresh, rfl⟩

def object (project : Object → Option runtime) (r : DataRelation runtime native) : DataRelation Object native where
  Holds heap object native footprint := ∃ value, project object = some value ∧ r.Holds heap value native footprint
  allocated := by rintro _ _ _ _ ⟨_, _, h⟩; exact r.allocated h
  frame := by rintro _ _ _ _ _ ⟨value, lookup, h⟩ eq; exact ⟨value, lookup, r.frame h eq⟩

def unit : DataRelation Value Unit := scalar (fun value _ => value = .undefined)
def bool : DataRelation Value Bool := scalar (fun value native => value = .boolean native)
def int : DataRelation Value Int := scalar (fun value native => value = .bigint native)
def int53 : DataRelation Value Int := scalar (fun value native =>
  Int53.InRange native ∧ value = .number (Float.Model.ofInt native))
def number : DataRelation Value Float.Model := scalar (fun value native => value = .number native)
def string : DataRelation Value JSString := scalar (fun value native => value = .string native)
def literal (expected : Value) : DataRelation Value Unit := scalar (fun value _ => value = expected)

def option (r : DataRelation Value α) : DataRelation Value (Option α) where
  Holds heap value native footprint := match native with
    | none => value = .undefined ∧ footprint = []
    | some native => r.Holds heap value native footprint
  allocated := by
    intro heap value native footprint h
    cases native with
    | none => rcases h with ⟨_, rfl⟩; simp [Allocated]
    | some native => exact r.allocated h
  frame := by
    intro before after value native footprint h eq
    cases native with
    | none => exact h
    | some native => exact r.frame h eq

def sum (left : DataRelation Value α) (right : DataRelation Value β) : DataRelation Value (Sum α β) where
  Holds heap value native footprint := match native with
    | .inl a => left.Holds heap value a footprint
    | .inr b => right.Holds heap value b footprint
  allocated := by
    intro heap value native footprint h
    cases native with
    | inl a => exact left.allocated h
    | inr b => exact right.allocated h
  frame := by
    intro before after value native footprint h eq
    cases native with
    | inl a => exact left.frame h eq
    | inr b => exact right.frame h eq

def array (element : DataRelation Value α) : DataRelation Value (List α) :=
  (reference (object (fun | .array values => some values | _ => none) element.sequence)).refine
    (fun values => values.length < 2 ^ 32)

/-- Record fields are selected by source names, not by heap field order. -/
def fieldsNil : DataRelation (List (String × Value)) Unit := scalar (fun _ _ => True)

def field (name : String) (head : DataRelation Value α)
    (tail : DataRelation (List (String × Value)) β) : DataRelation (List (String × Value)) (α × β) where
  Holds heap fields native footprint := ∃ value, fields.lookup name = some value ∧
    (head.product tail).Holds heap (value, fields) native footprint
  allocated := by rintro _ _ _ _ ⟨_, _, h⟩; exact (head.product tail).allocated h
  frame := by rintro _ _ _ _ _ ⟨value, lookup, h⟩ eq
              exact ⟨value, lookup, (head.product tail).frame h eq⟩

def record (fields : DataRelation (List (String × Value)) α) : DataRelation Value α :=
  reference (object (fun | .record values => some values | _ => none) fields)

def classState (name : String) (fields : DataRelation (List (String × Value)) α) : DataRelation Value α :=
  reference (object (fun | .instance_ actual values => if actual = name then some values else none | _ => none) fields)

def map [BEq κ] (key : DataRelation Value κ) (value : DataRelation Value υ) : DataRelation Value (JSMap κ υ) :=
  (reference (object (fun | .map entries => some entries | _ => none) (key.product value).sequence)).comap JSMap.entries

def set [BEq κ] (key : DataRelation Value κ) : DataRelation Value (JSSet κ) :=
  (reference (object (fun | .set values => some values | _ => none) key.sequence)).comap JSSet.values

def numberMap (value : DataRelation Value υ) : DataRelation Value (NumberMap υ) :=
  (@map Float.Model υ NumberKey.equality number value).refine NumberMap.Normalized

def numberSet : DataRelation Value NumberSet :=
  (@set Float.Model NumberKey.equality number).refine
    (fun values => ∀ key ∈ NumberSet.values values, NumberKey.normalize key = key)

def named (declaration : Named.Declaration) (interp : Named.Interp)
    (layout : DataRelation Value declaration.shape.denote) : DataRelation Value (interp declaration).Native :=
  layout.comap (interp declaration).destruct

theorem named_construct (declaration : Named.Declaration) (interp : Named.Interp)
    (layout : DataRelation Value declaration.shape.denote) (heap : Heap) (value : Value)
    (native : declaration.shape.denote) (footprint : Footprint) :
    (named declaration interp layout).Holds heap value ((interp declaration).construct native) footprint ↔
      layout.Holds heap value native footprint := by
  simp [named, comap, (interp declaration).destruct_construct]

theorem preserve {layout : DataRelation runtime native} {before after : Heap}
    {value : runtime} {native : native} {observed owned : Footprint}
    (input : layout.Holds before value native observed) (writes : Modifies owned before after)
    (separate : Disjoint observed owned) : layout.Holds after value native observed :=
  layout.frame input (writes.frame (layout.allocated input) separate)

theorem reference_allocate (contents : DataRelation Object α) (s : State)
    (object : Object) (native : α) (children : Footprint)
    (input : contents.Holds s.heap object native children) :
    (contents.reference).Holds (s.alloc object).2.heap (.ref (s.alloc object).1) native
      ((s.alloc object).1 :: children) := by
  exact ⟨_, object, children, rfl, s.alloc_lookup object,
    contents.frame input (s.alloc_frame object children (contents.allocated input)),
    s.alloc_fresh object children (contents.allocated input), rfl⟩

theorem array_allocate (element : DataRelation Value α) (s : State)
    (values : List Value) (natives : List α) (children : Footprint)
    (input : Elements element s.heap values natives children) (bound : natives.length < 2 ^ 32) :
    (array element).Holds (s.alloc (.array values)).2.heap (.ref (s.alloc (.array values)).1) natives
      ((s.alloc (.array values)).1 :: children) := by
  refine ⟨bound, ?_⟩
  apply reference_allocate
  exact ⟨values, rfl, input⟩

end DataRelation
end Ariadne.Shallow

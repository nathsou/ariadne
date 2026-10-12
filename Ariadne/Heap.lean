import Ariadne.Value

namespace Ariadne

/-- The operational heap, with stable natural-number addresses. -/
abbrev Heap := List Object

namespace Heap

/-- A finite set of addresses. Multiplicity and order do not affect framing. -/
abbrev Footprint := List Nat

def Allocated (heap : Heap) (footprint : Footprint) : Prop :=
  ∀ address ∈ footprint, address < heap.length

def Disjoint (left right : Footprint) : Prop :=
  ∀ address ∈ left, address ∉ right

/-- Equality of the cells that a representation is allowed to inspect. -/
def AgreesOn (footprint : Footprint) (before after : Heap) : Prop :=
  ∀ address ∈ footprint, before[address]? = after[address]?

/-- A computation may allocate fresh cells and write within its owned footprint.
Every old cell outside that footprint is preserved. -/
def Modifies (owned : Footprint) (before after : Heap) : Prop :=
  before.length ≤ after.length ∧
    ∀ address, address < before.length → address ∉ owned →
      before[address]? = after[address]?

theorem Disjoint.symm {a b : Footprint} (h : Disjoint a b) : Disjoint b a := by
  intro address hb ha
  exact h address ha hb

theorem AgreesOn.refl (heap : Heap) (footprint : Footprint) : AgreesOn footprint heap heap :=
  fun _ _ => rfl

theorem AgreesOn.symm {footprint : Footprint} {a b : Heap}
    (h : AgreesOn footprint a b) : AgreesOn footprint b a := fun i hi => (h i hi).symm

theorem AgreesOn.trans {footprint : Footprint} {a b c : Heap}
    (ab : AgreesOn footprint a b) (bc : AgreesOn footprint b c) : AgreesOn footprint a c :=
  fun i hi => (ab i hi).trans (bc i hi)

theorem AgreesOn.mono {small large : Footprint} {a b : Heap}
    (h : AgreesOn large a b) (subset : small ⊆ large) : AgreesOn small a b :=
  fun i hi => h i (subset hi)

theorem AgreesOn.append {left right : Footprint} {a b : Heap}
    (hl : AgreesOn left a b) (hr : AgreesOn right a b) : AgreesOn (left ++ right) a b := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hl i hi
  · exact hr i hi

theorem AgreesOn.allocated {footprint : Footprint} {a b : Heap}
    (h : AgreesOn footprint a b) (valid : Allocated a footprint) : Allocated b footprint := by
  intro i hi
  have present : a[i]? ≠ none := by simp; exact valid i hi
  rw [h i hi] at present
  simpa [List.getElem?_eq_none_iff] using present

theorem agreesOn_append (heap extra : Heap) (footprint : Footprint)
    (valid : Allocated heap footprint) : AgreesOn footprint heap (heap ++ extra) :=
  fun i hi => (List.getElem?_append_left (valid i hi)).symm

theorem agreesOn_set (heap : Heap) (footprint : Footprint) (address : Nat) (object : Object)
    (outside : address ∉ footprint) : AgreesOn footprint heap (heap.set address object) := by
  intro i hi
  exact (List.getElem?_set_ne (by intro eq; subst i; exact outside hi)).symm

theorem Modifies.refl (heap : Heap) (owned : Footprint) : Modifies owned heap heap :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

/-- A fresh allocation does not modify any old cell. -/
theorem modifies_append (heap extra : Heap) (owned : Footprint) : Modifies owned heap (heap ++ extra) :=
  ⟨by simp, fun _ hi _ => (List.getElem?_append_left hi).symm⟩

theorem modifies_set (heap : Heap) (owned : Footprint) (address : Nat) (object : Object)
    (member : address ∈ owned) : Modifies owned heap (heap.set address object) := by
  refine ⟨by simp, ?_⟩
  intro i _ outside
  exact (List.getElem?_set_ne (by intro eq; subst i; exact outside member)).symm

theorem Modifies.trans {owned : Footprint} {a b c : Heap}
    (ab : Modifies owned a b) (bc : Modifies owned b c) : Modifies owned a c := by
  refine ⟨Nat.le_trans ab.1 bc.1, ?_⟩
  intro i hi outside
  exact (ab.2 i hi outside).trans (bc.2 i (Nat.lt_of_lt_of_le hi ab.1) outside)

/-- The frame rule: a disjoint, allocated observation survives owned mutation. -/
theorem Modifies.frame {owned observed : Footprint} {a b : Heap}
    (writes : Modifies owned a b) (valid : Allocated a observed)
    (separate : Disjoint observed owned) : AgreesOn observed a b :=
  fun i hi => writes.2 i (valid i hi) (separate i hi)

end Heap

theorem State.alloc_fresh (s : State) (object : Object) (footprint : Heap.Footprint)
    (valid : Heap.Allocated s.heap footprint) : (s.alloc object).1 ∉ footprint := by
  intro member
  have := valid _ member
  simp [State.alloc] at this

theorem State.alloc_lookup (s : State) (object : Object) :
    (s.alloc object).2.heap[(s.alloc object).1]? = some object := by
  simp [State.alloc]

theorem State.alloc_frame (s : State) (object : Object) (footprint : Heap.Footprint)
    (valid : Heap.Allocated s.heap footprint) :
    Heap.AgreesOn footprint s.heap (s.alloc object).2.heap :=
  Heap.agreesOn_append s.heap [object] footprint valid

theorem State.write_modifies {s after : State} {address : Nat} {object : Object}
    (written : s.write address object = .ok after) : Heap.Modifies [address] s.heap after.heap := by
  unfold State.write at written
  split at written
  · cases written
    exact Heap.modifies_set _ _ _ _ (by simp)
  · cases written

end Ariadne

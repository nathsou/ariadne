import Ariadne.Shallow.Adequacy.Array
import Ariadne.Shallow.Adequacy.Record
import Ariadne.SourceFrom

namespace Ariadne.Shallow
open Heap DataRelation

theorem DataRelation.Elements.append {element : DataRelation runtime α} {heap : Heap}
    {left right : List runtime} {a b : List α} {fl fr : Footprint}
    (hl : Elements element heap left a fl) (hr : Elements element heap right b fr)
    (separate : Disjoint fl fr) : Elements element heap (left ++ right) (a ++ b) (fl ++ fr) := by
  induction hl with
  | nil => exact hr
  | @cons value native head values natives tail hv ht split ih =>
    have tailSeparate : Disjoint tail fr := fun i hi => separate i (by simp [hi])
    have headSeparate : Disjoint head (tail ++ fr) := by
      intro i hi member
      rcases List.mem_append.mp member with member | member
      · exact split i hi member
      · exact separate i (by simp [hi]) member
    simpa only [List.cons_append, List.append_assoc] using
      Elements.cons hv (ih tailSeparate) headSeparate

namespace Adequacy

/-- An owned push writes only the array root. The inserted value must be owned
separately from that root and the old elements; existing observations are framed. -/
theorem array_push {element : DataRelation Value α} {program : Program} {state : State}
    {receiver inserted : Value} {values : List α} {native : α} {owned fresh : Footprint}
    (array : element.array.Holds state.heap receiver values owned)
    (value : element.Holds state.heap inserted native fresh)
    (separate : Disjoint owned fresh) (capacity : (values ++ [native]).length < 2 ^ 32) :
    ∃ address after children,
      receiver = .ref address ∧
      Invokes program state (.method address "push") [inserted]
        (.number (Float.Model.ofNat (values ++ [native]).length)) after ∧
      element.array.Holds after.heap receiver (values ++ [native]) (address :: children) ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨address, runtime, children, rfl, lookup, related, rootFresh, rfl⟩ := array_contents array
  have childSeparate : Disjoint children fresh := fun i hi => separate i (by simp [hi])
  have rootSeparate : address ∉ fresh := separate address (by simp)
  have singleton : Elements element state.heap [inserted] [native] fresh := by
    simpa only [List.append_nil] using Elements.cons value Elements.nil (by simp [Disjoint])
  have combined := related.append singleton childSeparate
  have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  let contents := DataRelation.object (fun | .array xs => some xs | _ => none) element.sequence
  have packed : contents.Holds state.heap (.array (runtime ++ [inserted])) (values ++ [native]) (children ++ fresh) :=
    ⟨_, rfl, combined⟩
  have newFresh : address ∉ children ++ fresh := by simp [rootFresh, rootSeparate]
  obtain ⟨after, written, output, modifies⟩ := reference_write contents state address _ _ _ allocated packed newFresh
  refine ⟨address, after, children ++ fresh, rfl, ?_, ⟨capacity, output⟩, modifies⟩
  have allowed : ¬runtime.length ≥ 4294967295 := by
    change (values ++ [native]).length < 4294967296 at capacity
    simp only [List.length_append, List.length_singleton] at capacity
    rw [related.length]
    omega
  have allowedNative : ¬values.length ≥ 4294967295 := by simpa only [related.length] using allowed
  refine ⟨(by intro h; cases h), 1, ?_⟩
  simp [apply, lookup, written, related.length, allowedNative, pure, Except.pure, bind, Except.bind]

end Adequacy
end Ariadne.Shallow

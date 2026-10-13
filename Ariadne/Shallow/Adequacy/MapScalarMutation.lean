import Ariadne.Shallow.Adequacy.Map
import Ariadne.Shallow.Adequacy.Record
import Ariadne.Ownership.Sound

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Scalar insertion cannot introduce a borrowed reference or a new footprint.
Existing key identities and insertion order follow the original Map semantics. -/
theorem entries_set_scalar [BEq κ] {keyCodec : Value → κ → Prop} {valueCodec : Value → υ → Prop}
    {heap : Heap} {runtime : List (Value × Value)} {natives : List (κ × υ)} {owned : Footprint}
    (input : Elements ((DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) heap runtime natives owned)
    (query : κ) (sourceKey sourceValue : Value) (updated : υ)
    (keys : ∀ {source native}, keyCodec source native → sameValueZero source sourceKey = (native == query))
    (canonical : keyCodec (canonicalKey sourceKey) query) (encoded : valueCodec sourceValue updated) :
    Elements ((DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) heap
      (mapSet runtime sourceKey sourceValue) (MapEntries.set natives query updated) owned := by
  induction input with
  | nil =>
    exact Elements.cons (r := (DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) ⟨[], [], ⟨canonical, rfl⟩, ⟨encoded, rfl⟩, by simp [Disjoint], rfl⟩ .nil (by simp [Disjoint])
  | @cons entry native head entries natives tail pair rest separate ih =>
    rcases entry with ⟨key, value⟩
    rcases native with ⟨nativeKey, nativeValue⟩
    rcases pair with ⟨fk, fv, ⟨keyRelated, rfl⟩, ⟨valueRelated, rfl⟩, _, rfl⟩
    have same := keys keyRelated
    simp only [mapSet, MapEntries.set, same]
    split
    · exact Elements.cons (r := (DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) ⟨[], [], ⟨keyRelated, rfl⟩, ⟨encoded, rfl⟩, by simp [Disjoint], rfl⟩ rest separate
    · exact Elements.cons (r := (DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) ⟨[], [], ⟨keyRelated, rfl⟩, ⟨valueRelated, rfl⟩, by simp [Disjoint], rfl⟩ ih separate

/-- Scalar Map set is an actual invocation that writes only the Map root.
No pairwise input-disjointness premise is needed for scalar keys and values. -/
theorem map_set_scalar [BEq κ] {keyCodec : Value → κ → Prop} {valueCodec : Value → υ → Prop}
    {program : Program} {state : State} {address : Nat} {native : JSMap κ υ} {owned : Footprint}
    (input : (DataRelation.map (DataRelation.scalar keyCodec) (DataRelation.scalar valueCodec)).Holds
      state.heap (.ref address) native owned)
    (query : κ) (sourceKey sourceValue : Value) (updated : υ)
    (keys : ∀ {source native}, keyCodec source native → sameValueZero source sourceKey = (native == query))
    (canonical : keyCodec (canonicalKey sourceKey) query) (encoded : valueCodec sourceValue updated) :
    ∃ after, Invokes program state (.method address "set") [sourceKey, sourceValue] (.ref address) after ∧
      (DataRelation.map (DataRelation.scalar keyCodec) (DataRelation.scalar valueCodec)).Holds
        after.heap (.ref address) (native.set query updated) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨root, entries, children, same, lookup, related, fresh, footprint⟩ := map_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  have updatedEntries := entries_set_scalar related query sourceKey sourceValue updated keys canonical encoded
  have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  let contents := DataRelation.object (fun | .map entries => some entries | _ => none)
    ((DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)).sequence
  have packed : contents.Holds state.heap (.map (mapSet entries sourceKey sourceValue))
      (native.set query updated).entries children := ⟨_, rfl, updatedEntries⟩
  obtain ⟨after, written, represented, modifies⟩ :=
    reference_write contents state address _ _ _ allocated packed fresh
  refine ⟨after, ?_, footprint ▸ represented, modifies⟩
  refine ⟨(by intro h; cases h), 1, ?_⟩
  simp [apply, lookup, written, bind, Except.bind, pure, Except.pure]

/-- Scalar Map keys and values contribute no descendant footprint. -/
theorem scalar_map_footprint [BEq κ] {keyCodec : Value → κ → Prop} {valueCodec : Value → υ → Prop}
    {heap : Heap} {address : Nat} {native : JSMap κ υ} {owned : Footprint}
    (input : (DataRelation.map (DataRelation.scalar keyCodec) (DataRelation.scalar valueCodec)).Holds
      heap (.ref address) native owned) : owned = [address] := by
  obtain ⟨root, entries, children, same, _, related, _, footprint⟩ := map_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  have empty : ∀ {runtime natives footprint},
      Elements ((DataRelation.scalar keyCodec).product (DataRelation.scalar valueCodec)) heap
        runtime natives footprint → footprint = [] := by
    intro runtime natives footprint related
    induction related with
    | nil => rfl
    | cons head tail separate ih =>
      obtain ⟨fk, fv, key, value, _, eq⟩ := head
      simp only [key.2, value.2, List.nil_append] at eq
      simp only [eq, ih, List.nil_append]
  simpa only [empty related] using footprint

end Ariadne.Shallow.Adequacy

namespace Ariadne.Ownership
open Heap

/-- A passing entry check separates scalar Maps by their actual layouts. -/
theorem scalar_maps_guard_disjoint [BEq κ] [BEq ν]
    {leftKey : Value → κ → Prop} {rightKey : Value → ν → Prop}
    {leftValue : Value → α → Prop} {rightValue : Value → β → Prop}
    {program : Program} {heap : Heap} {args : List Value} {check : ArgumentCheck}
    {left right : Nat} {a b : Footprint}
    {leftNative : Shallow.JSMap κ α} {rightNative : Shallow.JSMap ν β}
    (leftLayout : (Shallow.DataRelation.map (Shallow.DataRelation.scalar leftKey)
      (Shallow.DataRelation.scalar leftValue)).Holds heap (.ref left) leftNative a)
    (rightLayout : (Shallow.DataRelation.map (Shallow.DataRelation.scalar rightKey)
      (Shallow.DataRelation.scalar rightValue)).Holds heap (.ref right) rightNative b)
    (leftArg : args[check.left]? = some (.ref left)) (rightArg : args[check.right]? = some (.ref right))
    (passed : checkArgument program heap args check = .ok ()) : Disjoint a b := by
  rw [Shallow.Adequacy.scalar_map_footprint leftLayout, Shallow.Adequacy.scalar_map_footprint rightLayout]
  exact checkArgument_disjoint (EntryShape.flat program heap check left right) leftArg rightArg passed

end Ariadne.Ownership

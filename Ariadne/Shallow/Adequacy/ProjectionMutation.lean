import Ariadne.Shallow.Adequacy.Focus
import Ariadne.Shallow.Adequacy.ArrayMutation
import Ariadne.Ownership.Sound
import Ariadne.Shallow.Lens
import Ariadne.Shallow.Prelude.ArrayUpdate

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Push through one array projection. The outer array retains its runtime
references; only the selected inner array is written. The native outer value
uses get/modify/set, and no input-disjointness premise is needed. -/
theorem array_projection_push {relation : Value → α → Prop} {program : Program} {state : State}
    {outer : Nat} {natives : List (List α)} {owned : Footprint} {index : Nat} {old : List α}
    {inserted : Value} {native : α}
    (input : (DataRelation.scalar relation).array.array.Holds state.heap (.ref outer) natives owned)
    (found : natives[index]? = some old)
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    ∃ (receiver : Value) (address : Nat) (after : State),
      receiver = Value.ref address ∧
      Invokes program state (.method address "push") [inserted]
        (.number (Float.Model.ofNat (old ++ [native]).length)) after ∧
      (DataRelation.scalar relation).array.array.Holds after.heap (.ref outer)
        (natives.set index (old ++ [native])) owned ∧
      Modifies [address] state.heap after.heap ∧
      ∃ runtime, state.heap[outer]? = some (.array runtime) ∧ runtime[index]? = some (.ref address) := by
  obtain ⟨root, runtime, children, same, lookup, elements, rootFresh, footprintEq⟩ := array_contents input
  have rootEq : outer = root := Value.ref.inj same
  subst root
  obtain ⟨receiver, selected, runtimeFound, subset, represented, rebuild⟩ := elements.focus index old found
  obtain ⟨address, actual, below, receiverEq, _, _, _, selectedEq⟩ := array_contents represented
  subst receiver
  have selectedSingleton := Ownership.scalar_array_footprint represented
  obtain ⟨actualAddress, after, newChildren, receiverEq, invoked, updated, writes⟩ :=
    array_push represented (show (DataRelation.scalar relation).Holds state.heap inserted native [] from ⟨value, rfl⟩)
      (by simp [Disjoint]) capacity
  have addressEq : address = actualAddress := Value.ref.inj receiverEq
  subst actualAddress
  have newSingleton := Ownership.scalar_array_footprint updated
  have updatedSelected : (DataRelation.scalar relation).array.Holds after.heap (.ref address)
      (old ++ [native]) selected := by
    rw [selectedSingleton]
    simpa only [newSingleton] using updated
  have writesSelected : Modifies selected state.heap after.heap := by simpa only [selectedSingleton] using writes
  have updatedElements := rebuild after.heap (old ++ [native]) updatedSelected writesSelected
  have outside : outer ∉ selected := fun member => rootFresh (subset member)
  have rootAllocated : outer < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have unchanged := writesSelected.2 outer rootAllocated outside
  refine ⟨.ref address, address, after, rfl, invoked, ?_, writes,
    runtime, lookup, runtimeFound⟩
  rw [footprintEq]
  refine ⟨?_, outer, .array runtime, children, rfl, unchanged.symm.trans lookup,
    ⟨runtime, rfl, updatedElements⟩, rootFresh, rfl⟩
  simpa only [List.length_set] using input.1

/-- Map get/modify/set changes the represented selected value without copying
its runtime array or rewriting the Map root. Ordered keys remain unchanged. -/
theorem map_projection_push [BEq key] {codec : Value → key → Prop} {relation : Value → α → Prop}
    {program : Program} {state : State} {outer : Nat} {natives : JSMap key (List α)} {owned : Footprint}
    {query : key} {sourceQuery : Value} {old : List α} {inserted : Value} {native : α}
    (input : (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array).Holds
      state.heap (.ref outer) natives owned)
    (found : natives.get query = some old)
    (keys : ∀ {source native}, codec source native → sameValueZero source sourceQuery = (native == query))
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    ∃ (address : Nat) (after : State),
      Invokes program state (.method outer "get") [sourceQuery] (.ref address) state ∧
      Invokes program state (.method address "push") [inserted]
        (.number (Float.Model.ofNat (old ++ [native]).length)) after ∧
      (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array).Holds after.heap
        (.ref outer) (natives.set query (old ++ [native])) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨root, runtime, children, same, lookup, elements, rootFresh, footprintEq⟩ := map_contents input
  have rootEq : outer = root := Value.ref.inj same
  subst root
  obtain ⟨receiver, selected, runtimeFound, subset, represented, rebuild⟩ :=
    elements.focusKey query sourceQuery old found keys
  obtain ⟨address, actual, below, receiverFound, _, _, _, selectedEq⟩ := array_contents represented
  subst receiver
  rw [receiverFound] at represented rebuild
  have selectedSingleton := Ownership.scalar_array_footprint represented
  obtain ⟨actualAddress, after, newChildren, receiverEq, invoked, updated, writes⟩ :=
    array_push represented (show (DataRelation.scalar relation).Holds state.heap inserted native [] from ⟨value, rfl⟩)
      (by simp [Disjoint]) capacity
  have addressEq : address = actualAddress := Value.ref.inj receiverEq
  subst actualAddress
  have newSingleton := Ownership.scalar_array_footprint updated
  have updatedSelected : (DataRelation.scalar relation).array.Holds after.heap (.ref address)
      (old ++ [native]) selected := by
    rw [selectedSingleton]
    simpa only [newSingleton] using updated
  have writesSelected : Modifies selected state.heap after.heap := by simpa only [selectedSingleton] using writes
  have updatedElements := rebuild after.heap (old ++ [native]) updatedSelected writesSelected
  have outside : outer ∉ selected := fun member => rootFresh (subset member)
  have rootAllocated : outer < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have unchanged := writesSelected.2 outer rootAllocated outside
  refine ⟨address, after, ?_, invoked, ?_, writes⟩
  · refine ⟨(by intro h; cases h), 1, ?_⟩
    simp [apply, lookup, receiverFound, pure, Except.pure]
  · rw [footprintEq]
    exact ⟨outer, .map runtime, children, rfl, unchanged.symm.trans lookup,
      ⟨runtime, rfl, updatedElements⟩, rootFresh, rfl⟩

end Ariadne.Shallow.Adequacy

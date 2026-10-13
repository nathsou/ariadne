import Ariadne.Shallow.Adequacy.Focus
import Ariadne.Shallow.Prelude.ArrayUpdate
import Ariadne.Ownership.Guard

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

private theorem source_key_symmetric (left right : Value) :
    sameValueZero left right = sameValueZero right left := by
  cases left <;> cases right <;> try simp [sameValueZero, strictEqual, BEq.comm]
  exact NumberKey.equal_symmetric _ _

private theorem source_key_transitive {a b c : Value}
    (ab : sameValueZero a b = true) (bc : sameValueZero b c = true) :
    sameValueZero a c = true := by
  cases a <;> cases b <;> cases c <;>
    try simp_all [sameValueZero, strictEqual, beq_iff_eq]
  rename_i a b c
  have equal := NumberKey.equal_transitive (a := a) (b := b) (c := c)
    (by simpa [NumberKey.equal] using ab) (by simpa [NumberKey.equal] using bc)
  simpa [NumberKey.equal] using equal

/-- Passing the array key guard implies separation of the actual selected
heap footprints. Input separation is derived, rather than assumed. -/
theorem array_projection_guard {element : DataRelation Value α} {state : State}
    {outer : Nat} {natives : List α} {owned : Footprint}
    (input : element.array.Holds state.heap (.ref outer) natives owned)
    (left right : Float.Model) (a b : α)
    (foundLeft : JSArray.get natives left = some a)
    (foundRight : JSArray.get natives right = some b)
    (passed : Ownership.projectionEqual .array (.number left) (.number right) = false) :
    ∃ first second firstFootprint secondFootprint,
      readIndex state (.ref outer) (.number left) = .ok first ∧
      readIndex state (.ref outer) (.number right) = .ok second ∧
      firstFootprint ⊆ owned ∧ secondFootprint ⊆ owned ∧
      element.Holds state.heap first a firstFootprint ∧
      element.Holds state.heap second b secondFootprint ∧
      Disjoint firstFootprint secondFootprint := by
  cases leftIndex : indexOf (.number left) with
  | none => simp [JSArray.get, leftIndex] at foundLeft
  | some i =>
    cases rightIndex : indexOf (.number right) with
    | none => simp [JSArray.get, rightIndex] at foundRight
    | some j =>
      have selectedLeft : natives[i]? = some a := by simpa [JSArray.get, leftIndex] using foundLeft
      have selectedRight : natives[j]? = some b := by simpa [JSArray.get, rightIndex] using foundRight
      obtain ⟨root, values, children, same, lookup, related, _, rfl⟩ := array_contents input
      have sameRoot : outer = root := Value.ref.inj same
      subst root
      obtain ⟨first, second, fa, fb, ha, hb, sa, sb, ra, rb, separated⟩ :=
        related.focus_disjoint i j a b selectedLeft selectedRight
          (JSArray.index_guard_distinct leftIndex rightIndex passed)
      exact ⟨first, second, fa, fb,
        by simp [readIndex, leftIndex, lookup, ha, pure, Except.pure],
        by simp [readIndex, rightIndex, lookup, hb, pure, Except.pure],
        (fun _ member => List.mem_cons_of_mem _ (sa member)),
        (fun _ member => List.mem_cons_of_mem _ (sb member)), ra, rb, separated⟩

/-- Map equality is SameValueZero at both the guard and lookup. In particular,
two NaN keys cannot pass the guard and select the same value. -/
theorem map_projection_guard [BEq key] {codec : Value → key → Prop}
    {element : DataRelation Value α} {state : State} {outer : Nat}
    {natives : JSMap key α} {owned : Footprint}
    (input : (DataRelation.map (DataRelation.scalar codec) element).Holds state.heap (.ref outer) natives owned)
    (left right : key) (sourceLeft sourceRight : Value) (a b : α)
    (foundLeft : natives.get left = some a) (foundRight : natives.get right = some b)
    (keysLeft : ∀ {source native}, codec source native → sameValueZero source sourceLeft = (native == left))
    (keysRight : ∀ {source native}, codec source native → sameValueZero source sourceRight = (native == right))
    (passed : Ownership.projectionEqual .map sourceLeft sourceRight = false) :
    ∃ entries first second firstFootprint secondFootprint,
      state.heap[outer]? = some (.map entries) ∧
      mapGet entries sourceLeft = first ∧ mapGet entries sourceRight = second ∧
      firstFootprint ⊆ owned ∧ secondFootprint ⊆ owned ∧
      element.Holds state.heap first a firstFootprint ∧
      element.Holds state.heap second b secondFootprint ∧
      Disjoint firstFootprint secondFootprint := by
  obtain ⟨root, entries, children, same, lookup, related, _, rfl⟩ := map_contents input
  have sameRoot : outer = root := Value.ref.inj same
  subst root
  have different : ∀ {source candidate}, codec source candidate →
      (candidate == left) = true → (candidate == right) = true → False := by
    intro source candidate encoded matchesLeft matchesRight
    have atLeft : sameValueZero source sourceLeft = true := (keysLeft encoded).trans matchesLeft
    have atRight : sameValueZero source sourceRight = true := (keysRight encoded).trans matchesRight
    have overlap := source_key_transitive ((source_key_symmetric sourceLeft source).trans atLeft) atRight
    change sameValueZero sourceLeft sourceRight = false at passed
    rw [passed] at overlap
    contradiction
  obtain ⟨first, second, fa, fb, ha, hb, sa, sb, ra, rb, separated⟩ :=
    related.focusKey_disjoint left right sourceLeft sourceRight a b
      foundLeft foundRight keysLeft keysRight different
  exact ⟨entries, first, second, fa, fb, lookup, ha, hb,
    (fun _ member => List.mem_cons_of_mem _ (sa member)),
    (fun _ member => List.mem_cons_of_mem _ (sb member)), ra, rb, separated⟩

end Ariadne.Shallow.Adequacy

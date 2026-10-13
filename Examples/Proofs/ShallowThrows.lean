import Examples.Shallow.throws

/-!
Proofs about emitted throwing functions. A function that can throw returns
`Sum.inl message` where the source throws `new Error(message)`, and `Sum.inr`
of its result otherwise.
-/

namespace Examples.Proofs.ShallowThrows
open Ariadne.Shallow Extracted_throws.Shallow

theorem checked_ok {x : Int} (nonnegative : 0 ≤ x) : «checked» x = .inr (x * 2) := by
  simp [«checked», Int.not_lt.mpr nonnegative]

theorem checked_throws {x : Int} (negative : x < 0) : ∃ message, «checked» x = .inl message := by
  simp [«checked», negative]

/-- A returned call to a throwing function propagates its error unchanged. -/
theorem relay_eq (x : Int) : «relay» x = «checked» (x - 1) := by
  simp [«relay», «checked»]

theorem validate_ok {n : Int} (nonzero : n ≠ 0) : «validate» n = .inr () := by
  simp [«validate», nonzero]

theorem always_throws : ∃ message, «always» = .inl message := ⟨_, rfl⟩

end Examples.Proofs.ShallowThrows

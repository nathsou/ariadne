import Examples.Shallow.scalars

namespace Examples.Proofs.ShallowScalars
open Extracted_scalars.Shallow

/-- This proof concerns the emitted native definition only. Source transfer
requires the separate operational adequacy milestone. -/
theorem abs_nonneg (x : Int) : 0 ≤ abs x := by
  unfold abs
  split <;> simp_all <;> omega

theorem abs_of_nonneg (x : Int) (h : 0 ≤ x) : abs x = x := by
  simp [abs, show ¬x < 0 by omega]

theorem abs_idempotent (x : Int) : abs (abs x) = abs x :=
  abs_of_nonneg _ (abs_nonneg x)

theorem scoped_formula (x : Int) : «scoped» x = 2 * x - 1 := by
  simp only [«scoped»]
  omega

theorem fallback_present (x : Int) : fallback (some x) = x := rfl

theorem optional_present (x : Int) : optional true x = some x := rfl

end Examples.Proofs.ShallowScalars

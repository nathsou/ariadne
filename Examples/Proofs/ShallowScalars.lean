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
  simp [«scoped»] <;> omega

theorem fallback_present (x : Int) : fallback (some x) = x := rfl

theorem optional_present (x : Int) : optional true x = some x := rfl

theorem guarded_present (x floor : Int) : guarded (some x) floor = x + 1 := rfl

theorem forget_clear (x : Option Int) : forget x true = none := by
  cases x <;> simp [forget]

theorem scopedTypes_formula (x : Int) : scopedTypes x = if x > 0 then x + 1 else x := by
  simp [scopedTypes]

end Examples.Proofs.ShallowScalars

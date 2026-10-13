import Examples.Shallow.recursion

/-!
Proofs about emitted measured recursive functions. A measured recursive
function denotes recursion bounded by its measure; once its body is shown to
call itself only on smaller measures, `Measured.fixBounded_unfold` gives its
fixpoint equation and proofs proceed by induction on the measure.
-/

namespace Examples.Proofs.ShallowRecursion
open Ariadne.Shallow Extracted_recursion.Shallow

/-- `factorial` calls itself only on a smaller nonnegative measure. -/
private theorem factorial_decreasing :
    Measured.Decreasing (fun x => (JoinNative.«factorial#0» x).toNat)
      (fun self args => if decide (args.1 ≤ 0) then 1 else args.1 * self (args.1 - 1, ())) := by
  intro f g x same
  simp only
  split
  · rfl
  · rename_i positive
    simp only [decide_eq_true_eq, Int.not_le] at positive
    rw [same]
    simp only [JoinNative.«factorial#0»]
    omega

theorem factorial_zero : «factorial» 0 = 1 := by
  simp [«factorial», JoinNative.«factorial#1», Measured.fixBounded, Measured.recurse]

/-- The recurrence the source states, for every positive argument. -/
theorem factorial_succ {n : Int} (positive : 0 < n) : «factorial» n = n * «factorial» (n - 1) := by
  simp only [«factorial», JoinNative.«factorial#1»]
  rw [Measured.fixBounded_unfold _ _ _ factorial_decreasing]
  simp [Int.not_le.mpr positive]

end Examples.Proofs.ShallowRecursion

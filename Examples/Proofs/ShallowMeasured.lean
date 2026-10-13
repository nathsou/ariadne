import Examples.Shallow.measured

/-!
Proofs about emitted measured loops. A measured loop denotes bounded iteration;
once its measure is shown to decrease, `Measured.bounded_unfold` gives the
loop's unfolding equation and the proof proceeds by induction on the measure.
-/

namespace Examples.Proofs.ShallowMeasured
open Ariadne.Shallow Extracted_measured.Shallow

/-- Every continuing step of `countdown` lowers `i`. -/
private theorem countdown_decreases (s next : Int × Int × Int × Unit)
    (step : JoinNative.«countdown#1» s = .next next) :
    (JoinNative.«countdown#0» next).toNat < (JoinNative.«countdown#0» s).toNat := by
  simp only [JoinNative.«countdown#1»] at step
  split at step
  · rename_i positive
    cases step
    simp only [JoinNative.«countdown#0», decide_eq_true_eq] at positive ⊢
    omega
  · cases step

private theorem countdown_loop (n : Int) : ∀ (k : Nat) (steps i : Int), i.toNat = k →
    ∃ i', Measured.bounded JoinNative.«countdown#0» (steps, i, n, ()) JoinNative.«countdown#1» =
      .done (steps + i.toNat, i', n, ()) := by
  intro k
  induction k with
  | zero =>
    intro steps i hi
    refine ⟨i, ?_⟩
    rw [Measured.bounded_unfold _ _ _ countdown_decreases]
    have : ¬ (0 : Int) < i := by omega
    simp [JoinNative.«countdown#1», this, hi]
  | succ k ih =>
    intro steps i hi
    obtain ⟨i', h⟩ := ih (steps + 1) (i - 1) (by omega)
    refine ⟨i', ?_⟩
    rw [Measured.bounded_unfold _ _ _ countdown_decreases]
    have pos : (0 : Int) < i := by omega
    simp only [JoinNative.«countdown#1», pos, decide_true, ↓reduceIte, h]
    congr 2
    omega

/-- `countdown n` counts the steps from `n` down to zero. -/
theorem countdown_eq (n : Int) : «countdown» n = n.toNat := by
  obtain ⟨i', h⟩ := countdown_loop n n.toNat 0 n rfl
  simp [«countdown», h, Exit.elim]

end Examples.Proofs.ShallowMeasured


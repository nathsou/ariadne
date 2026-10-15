import Examples.Clamp

/-!
# Proofs about `clamp`

`Examples/Clamp.lean` is generated from `clamp.ts`. Its readable definition `clamp` is plain Lean, so
properties are proved about it with ordinary tactics; the generated theorem `clamp.source` then carries
them to every run of the JavaScript function.
-/

namespace Examples.Clamp.Proofs
open Ariadne Examples.Clamp

/-- With `lo ≤ hi`, the result lies in the range. -/
theorem clamp_between (x lo hi : Int) (h : lo ≤ hi) : lo ≤ clamp x lo hi ∧ clamp x lo hi ≤ hi := by
  unfold clamp
  split
  · omega
  · split <;> simp_all <;> omega

/-- A value already in the range is left alone. -/
theorem clamp_of_inRange (x lo hi : Int) (h : inRange x lo hi = true) : clamp x lo hi = x := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  simp [clamp]
  omega

/-- The two functions agree: a clamped value is in the range. -/
theorem inRange_clamp (x lo hi : Int) (h : lo ≤ hi) : inRange (clamp x lo hi) lo hi = true := by
  have := clamp_between x lo hi h
  simp [inRange]
  omega

/-- Clamping twice is clamping once. -/
theorem clamp_idempotent (x lo hi : Int) (h : lo ≤ hi) : clamp (clamp x lo hi) lo hi = clamp x lo hi :=
  clamp_of_inRange _ _ _ (inRange_clamp x lo hi h)

/-- **The claim about the JavaScript.** Every run of `clamp(x, lo, hi)`, on arguments representing
`x`, `lo` and `hi`, with `lo ≤ hi`, returns a number between `lo` and `hi`. -/
theorem clamp_run (x lo hi : Int) (vs : List JSValue) (args : ArgsRep sig.clamp.params vs (x, lo, hi, ()))
    (h : lo ≤ hi) :
    ∃ n : Int, Converges (fun fuel => run ast fuel "clamp" vs) (.ok (.number n)) ∧ lo ≤ n ∧ n ≤ hi := by
  obtain ⟨w, runs, rep⟩ := clamp.source x lo hi vs args
  simp only [Ty.Rep] at rep
  subst rep
  exact ⟨_, runs, clamp_between x lo hi h⟩

end Examples.Clamp.Proofs

import Examples.Shallow.arrays

namespace Examples.Proofs.ShallowArrays
open Extracted_arrays.Shallow (copy transform sum score)
open Ariadne.Shallow

theorem copy_eq (xs : List Int) : copy xs = xs := rfl

theorem sum_eq_foldl (xs : List Int) : sum xs = xs.foldl (· + ·) 0 := by
  simp [sum]

theorem sum_permutation {xs ys : List Int} (permutation : xs.Perm ys) : sum xs = sum ys := by
  simp only [sum_eq_foldl]
  apply permutation.foldl_eq'
  intros
  omega

theorem transform_nonnegative (xs : List Int) (delta : Int) (nonnegative : 0 ≤ delta) :
    ∀ y ∈ transform xs delta, 0 ≤ y := by
  simp only [transform, JSArray.map_unindexed, JSArray.filter_unindexed]
  intro y member
  obtain ⟨x, included, rfl⟩ := List.mem_map.mp member
  simp only [List.mem_filter, decide_eq_true_eq] at included
  omega

theorem score_formula (xs : List Int) : score xs = sum xs + 1 := by
  simp [score, sum]

end Examples.Proofs.ShallowArrays

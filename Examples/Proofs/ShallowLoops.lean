import Examples.Shallow.loops

namespace Examples.Proofs.ShallowLoops
open Ariadne.Shallow Extracted_loops.Shallow

private theorem sum_loop (xs captured : List Int) (initial : Int) :
    Exit.elim (Loop.each xs (initial, captured, ()) JoinNative.«sum#0»)
      JoinNative.«sum#1» id = xs.foldl (· + ·) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => simpa only [Loop.each, JoinNative.«sum#0», List.foldl_cons] using ih (initial + x)

theorem sum_fold (xs : List Int) : sum xs = xs.foldl (· + ·) 0 :=
  sum_loop xs xs 0

theorem sum_permutation {xs ys : List Int} (permutation : xs.Perm ys) : sum xs = sum ys := by
  simp only [sum_fold]
  apply permutation.foldl_eq'
  intros
  omega

theorem sum_append (xs ys : List Int) : sum (xs ++ ys) = sum xs + sum ys := by
  simp only [sum_fold, List.foldl_append]
  have shift : ∀ (xs : List Int) (a b : Int),
      xs.foldl (· + ·) (a + b) = a + xs.foldl (· + ·) b := by
    intro xs a b
    induction xs generalizing b with
    | nil => rfl
    | cons x xs ih => simpa only [List.foldl_cons, Int.add_assoc] using ih (b + x)
  simpa using shift ys (xs.foldl (· + ·) 0) 0

private theorem first_loop (xs captured : List Int) (floor : Int) :
    Exit.elim (Loop.each xs (captured, floor, ()) JoinNative.«first#0»)
      JoinNative.«first#1» id = xs.find? (fun x => decide (floor ≤ x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : floor ≤ x
    · simp [Loop.each, JoinNative.«first#0», h, Exit.elim, List.find?]
    · simpa only [Loop.each, JoinNative.«first#0», h, decide_false, Bool.false_eq_true,
        ite_false, List.find?] using ih

theorem first_find (xs : List Int) (floor : Int) :
    first xs floor = xs.find? (fun x => decide (floor ≤ x)) := first_loop xs xs floor

theorem first_member {xs : List Int} {floor value : Int} (found : first xs floor = some value) : value ∈ xs := by
  rw [first_find] at found
  exact List.mem_of_find?_eq_some found

theorem first_floor {xs : List Int} {floor value : Int} (found : first xs floor = some value) : floor ≤ value := by
  rw [first_find] at found
  exact of_decide_eq_true (List.find?_some (p := fun x : Int => decide (floor ≤ x)) found)

end Examples.Proofs.ShallowLoops

import Examples.Shallow.collections

namespace Examples.Proofs.ShallowCollections
open Ariadne Ariadne.Shallow Extracted_collections.Shallow

theorem read_lookup (m : JSMap JSString Int) (key : JSString) : read m key = m.get key := rfl

theorem readDefault_lookup (m : JSMap JSString Int) (key : JSString) :
    readDefault m key = (m.get key).getD 9 := by
  cases h : m.get key <;> simp [readDefault, h, Option.getD]

private theorem histogram_loop (xs captured : List JSString) (initial : JSMap JSString Int) :
    Exit.elim (Loop.each xs (initial, captured, ()) JoinNative.«histogram#0»)
      JoinNative.«histogram#1» id =
      xs.foldl (fun m x => m.set x ((m.get x).getD 0 + 1)) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    have default : (initial.get x).elim 0 (fun value => value) = (initial.get x).getD 0 := by
      cases initial.get x <;> rfl
    simpa only [Loop.each, JoinNative.«histogram#0», List.foldl_cons, default]
      using ih (initial.set x ((initial.get x).getD 0 + 1))

theorem histogram_fold (xs : List JSString) :
    histogram xs = xs.foldl (fun m x => m.set x ((m.get x).getD 0 + 1)) JSMap.empty :=
  histogram_loop xs xs JSMap.empty

private theorem fold_count (xs : List JSString) (initial : JSMap JSString Int) (key : JSString) :
    ((xs.foldl (fun m x => m.set x ((m.get x).getD 0 + 1)) initial).get key).getD 0 =
      (initial.get key).getD 0 + (xs.count key : Int) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, JSMap.get_set, List.count_cons]
    by_cases h : x = key
    · subst x
      simp
      omega
    · simp [h, beq_iff_eq]

theorem histogram_count (xs : List JSString) (key : JSString) :
    ((histogram xs).get key).getD 0 = (xs.count key : Int) := by
  rw [histogram_fold, fold_count]
  simp

private theorem fold_has (xs : List JSString) (initial : JSMap JSString Int) (key : JSString) :
    (xs.foldl (fun m x => m.set x ((m.get x).getD 0 + 1)) initial).has key =
      (initial.has key || xs.contains key) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [JSMap.has, JSMap.get_set, List.contains_cons]
    by_cases h : x = key
    · subst x
      simp
    · have different : (key == x) = false := Bool.eq_false_iff.mpr (fun eq => h (eq_of_beq eq).symm)
      simp [h, different, beq_iff_eq]

theorem histogram_has (xs : List JSString) (key : JSString) :
    (histogram xs).has key = xs.contains key := by
  rw [histogram_fold, fold_has]
  rfl

theorem histogram_permutation {xs ys : List JSString} (permutation : xs.Perm ys) :
    JSMap.LookupEq (histogram xs) (histogram ys) := by
  intro key
  have counts : ((histogram xs).get key).getD 0 = ((histogram ys).get key).getD 0 := by
    simp only [histogram_count, permutation.count_eq key]
  have present : ((histogram xs).get key).isSome = ((histogram ys).get key).isSome := by
    change (histogram xs).has key = (histogram ys).has key
    simp only [histogram_has, permutation.contains_eq]
  cases hx : (histogram xs).get key <;> cases hy : (histogram ys).get key <;> simp_all

end Examples.Proofs.ShallowCollections

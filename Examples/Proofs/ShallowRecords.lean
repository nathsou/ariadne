import Examples.Shallow.records

namespace Examples.Proofs.ShallowRecords
open Ariadne.Shallow Extracted_records.Shallow
open NativeTypes

theorem make_fields (x : Int) (label : Ariadne.JSString) :
    (make x label).x = x ∧ (make x label).label = label ∧ (make x label).weight = none :=
  ⟨rfl, rfl, rfl⟩

theorem relabel_preserves (p : Point) (label : Ariadne.JSString) :
    (relabel p label).x = p.x ∧ (relabel p label).weight = p.weight := ⟨rfl, rfl⟩

theorem relabel_identity (p : Point) : relabel p p.label = p := by cases p; rfl

theorem relabel_overwrite (p : Point) (first last : Ariadne.JSString) :
    relabel (relabel p first) last = relabel p last := rfl

theorem tagged_payload (x : Int) : (tagged x).payload = x := rfl

theorem tagName_fixed (value : Tagged) : tagName value = [111, 107] := rfl

theorem unusual_fields (n : Int) : fields (weird n) = n + 2 := rfl

theorem duplicate_last_wins : duplicate.x = 2 ∧ duplicate.weight = none := ⟨rfl, rfl⟩

private theorem sum_loop (xs captured : List Point) (initial : Int) :
    Exit.elim (Loop.each xs (initial, captured, ()) JoinNative.«sum#0»)
      JoinNative.«sum#1» id = xs.foldl (fun total p => total + (p.x + p.weight.getD 0)) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    cases h : x.weight <;>
      simpa only [Loop.each, JoinNative.«sum#0», NativeDestruct.Point,
        List.foldl_cons, h, Option.elim, Option.getD] using ih (initial + (x.x + x.weight.getD 0))

theorem sum_fold (xs : List Point) :
    sum xs = xs.foldl (fun total p => total + (p.x + p.weight.getD 0)) 0 := sum_loop xs xs 0

theorem sum_permutation {xs ys : List Point} (permutation : xs.Perm ys) : sum xs = sum ys := by
  simp only [sum_fold]
  apply permutation.foldl_eq'
  intros
  omega

theorem find_spec (xs : List Point) (floor : Int) :
    find xs floor = xs.find? (fun p => decide (floor ≤ p.x)) := by
  unfold find JSArray.find NativeDestruct.Point
  have h := congrArg (List.find? (fun p : Point => decide (floor ≤ p.x))) (List.zipIdx_map_fst 0 xs)
  simpa only [List.find?_map, Function.comp_def] using h

theorem find_member {xs : List Point} {floor : Int} {value : Point}
    (found : find xs floor = some value) : value ∈ xs := by
  rw [find_spec] at found
  exact List.mem_of_find?_eq_some found

theorem find_floor {xs : List Point} {floor : Int} {value : Point}
    (found : find xs floor = some value) : floor ≤ value.x := by
  rw [find_spec] at found
  exact of_decide_eq_true (List.find?_some (p := fun p : Point => decide (floor ≤ p.x)) found)

end Examples.Proofs.ShallowRecords

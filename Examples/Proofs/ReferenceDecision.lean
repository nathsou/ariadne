import Examples.ShallowReference.decision
import Init.Data.Order.PackageFactories
import Init.Data.Order.LemmasExtra

namespace Examples.Proofs.ReferenceDecision
open Ariadne.Shallow Extracted_reference_decision.Shallow NativeTypes

def pick (floor : Int) (best : Option Candidate) (candidate : Candidate) : Option Candidate :=
  match candidate with
  | .rejected _ => best
  | .valid current =>
    if floor ≤ current.version then
      match best with
      | some (.valid previous) =>
        if decide (previous.version < current.version) ||
            (decide (current.version = previous.version) && (compare previous.id current.id == .lt)) then
          some candidate else best
      | _ => some candidate
    else best

theorem choose_step (candidate : Candidate) (best : Option Candidate)
    (captured : List Candidate) (floor : Int) :
    JoinNative.«choose#3» candidate (best, captured, floor, ()) =
      Step.next (pick floor best candidate, captured, floor, ()) := by
  cases candidate with
  | rejected rejected => simp [pick]
  | valid current =>
    by_cases floorOk : floor ≤ current.version
    case neg => simp [pick, floorOk]
    cases best with
    | none => simp [pick, floorOk]
    | some previous =>
      cases previous with
      | rejected rejected => simp [pick, floorOk]
      | valid previous =>
        by_cases less : previous.version < current.version <;>
          by_cases equal : current.version = previous.version <;>
          by_cases order : compare previous.id current.id = .lt <;>
          simp [pick, floorOk, less, equal, order] <;>
          cases current <;> cases previous <;> simp_all

private theorem choose_loop (xs captured : List Candidate) (floor : Int) (best : Option Candidate) :
    Exit.elim (Loop.each xs (best, captured, floor, ()) JoinNative.«choose#3»)
      JoinNative.«choose#4» id = xs.foldl (pick floor) best := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih => simpa only [Loop.each, choose_step, List.foldl_cons] using ih (pick floor best x)

theorem choose_fold (xs : List Candidate) (floor : Int) :
    choose xs floor = xs.foldl (pick floor) none := choose_loop xs xs floor none

theorem pick_origin (floor : Int) (best : Option Candidate) (candidate : Candidate) :
    pick floor best candidate = best ∨ pick floor best candidate = some candidate := by
  cases candidate with
  | rejected value => exact Or.inl rfl
  | valid current =>
    by_cases floorOk : floor ≤ current.version
    case neg => simp [pick, floorOk]
    cases best with
    | none => simp [pick, floorOk]
    | some previous =>
      cases previous with
      | rejected value => simp [pick, floorOk]
      | valid previous =>
        simp only [pick, floorOk, ite_true]
        split <;> simp

private theorem fold_origin (xs : List Candidate) (floor : Int) (best : Option Candidate) (value : Candidate)
    (found : xs.foldl (pick floor) best = some value) : value ∈ xs ∨ best = some value := by
  induction xs generalizing best with
  | nil => exact Or.inr found
  | cons x xs ih =>
    rcases ih (pick floor best x) found with member | chosen
    · exact Or.inl (List.mem_cons_of_mem x member)
    · rcases pick_origin floor best x with old | current
      · exact Or.inr (old.symm.trans chosen)
      · have equal := Option.some.inj (current.symm.trans chosen)
        exact Or.inl (by simp [equal])

theorem choose_member {xs : List Candidate} {floor : Int} {value : Candidate}
    (found : choose xs floor = some value) : value ∈ xs := by
  rw [choose_fold] at found
  rcases fold_origin xs floor none value found with member | impossible
  · exact member
  · cases impossible

def SafeBest (floor : Int) : Option Candidate → Prop
  | none => True
  | some (.valid value) => floor ≤ value.version
  | some (.rejected _) => False

theorem pick_safe (floor : Int) (best : Option Candidate) (candidate : Candidate)
    (safe : SafeBest floor best) : SafeBest floor (pick floor best candidate) := by
  cases candidate with
  | rejected value => exact safe
  | valid current =>
    by_cases floorOk : floor ≤ current.version
    case neg => simpa [pick, floorOk] using safe
    cases best with
    | none => simp [pick, floorOk, SafeBest]
    | some previous =>
      cases previous with
      | rejected value => cases safe
      | valid previous =>
        simp only [pick, floorOk, ite_true]
        split
        · exact floorOk
        · exact safe

private theorem fold_safe (xs : List Candidate) (floor : Int) (best : Option Candidate)
    (safe : SafeBest floor best) : SafeBest floor (xs.foldl (pick floor) best) := by
  induction xs generalizing best with
  | nil => exact safe
  | cons x xs ih => exact ih _ (pick_safe floor best x safe)

theorem choose_safe (xs : List Candidate) (floor : Int) : SafeBest floor (choose xs floor) := by
  rw [choose_fold]
  exact fold_safe xs floor none True.intro

theorem choose_floor {xs : List Candidate} {floor : Int} {value : «Candidate#left»}
    (found : choose xs floor = some (.valid value)) : floor ≤ value.version := by
  have safe := choose_safe xs floor
  rw [found] at safe
  exact safe

theorem choose_ne_rejected (xs : List Candidate) (floor : Int) (reason : «Candidate#right») :
    choose xs floor ≠ some (.rejected reason) := by
  intro found
  have safe := choose_safe xs floor
  rw [found] at safe
  exact safe

structure Rank where
  version : Int
  id : Ariadne.JSString
instance : Ord Rank := ⟨compareLex (compareOn Rank.version) (compareOn Rank.id)⟩
instance : Std.TransOrd Rank := inferInstanceAs (Std.TransCmp (compareLex _ _))
instance : Std.LawfulEqOrd Rank where
  eq_of_compare {a b} h := by
    change compareLex (compareOn Rank.version) (compareOn Rank.id) a b = .eq at h
    simp only [compareLex_eq_eq, compareOn] at h
    have hv := Std.LawfulEqOrd.eq_of_compare h.1
    have hi := Std.LawfulEqOrd.eq_of_compare h.2
    cases a; cases b; simp_all
instance : Std.LinearOrderPackage Rank := .ofOrd Rank
private theorem upper_eq {a b : Rank} (same : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  Std.le_antisymm ((same b).mpr (Std.le_refl b)) ((same a).mp (Std.le_refl a))
theorem max_comm (a b : Rank) : max a b = max b a := by
  apply upper_eq
  intro c
  simp only [Std.max_le_iff, and_comm]
theorem max_swap (z x y : Rank) : max (max z x) y = max (max z y) x := by
  apply upper_eq
  intro c
  simp only [Std.max_le_iff, and_assoc, and_left_comm, and_comm]
theorem compare_lt (a b : Rank) : compare a b = .lt ↔
    a.version < b.version ∨ a.version = b.version ∧ compare a.id b.id = .lt := by
  change (compare a.version b.version).then (compare a.id b.id) = .lt ↔ _
  simp [Ordering.then_eq_lt, Std.compare_eq_lt]
theorem max_pick (a b : Rank) : max a b =
    if decide (a.version < b.version) || (decide (b.version = a.version) && (compare a.id b.id == .lt)) then b else a := by
  have condition : (decide (a.version < b.version) || (decide (b.version = a.version) && (compare a.id b.id == .lt))) =
      (compare a b == .lt) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, compare_lt]
    rw [eq_comm (a := b.version) (b := a.version)]
  rw [Std.max_eq_ite_isGE_compare, condition]
  cases compare a b <;> rfl

def merge : Option Rank → Option Rank → Option Rank
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

theorem merge_swap (z x y : Option Rank) : merge (merge z x) y = merge (merge z y) x := by
  cases z with
  | none => cases x <;> cases y <;> simp [merge, max_comm]
  | some z =>
    cases x with
    | none => cases y <;> rfl
    | some x =>
      cases y with
      | none => rfl
      | some y => exact congrArg some (max_swap z x y)

def selected (floor : Int) : Candidate → Option Rank
  | .valid value => if floor ≤ value.version then some ⟨value.version, value.id⟩ else none
  | .rejected _ => none

def decode (value : Option Rank) : Option Candidate :=
  value.map fun rank => .valid ⟨rank.version, rank.id⟩

theorem pick_decode (floor : Int) (best : Option Rank) (candidate : Candidate) :
    pick floor (decode best) candidate = decode (merge best (selected floor candidate)) := by
  cases candidate with
  | rejected value => cases best <;> rfl
  | valid value =>
    by_cases allowed : floor ≤ value.version
    · cases best with
      | none => cases value; simp [pick, decode, merge, selected, allowed]
      | some previous =>
        simp only [selected, allowed, ite_true, merge, max_pick]
        cases value
        cases previous
        simp [pick, decode, allowed]
        split <;> simp_all
    · cases best <;> simp [pick, decode, merge, selected, allowed]

private theorem fold_decode (xs : List Candidate) (floor : Int) (best : Option Rank) :
    xs.foldl (pick floor) (decode best) =
      decode (xs.foldl (fun previous candidate => merge previous (selected floor candidate)) best) := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, pick_decode]
    exact ih _

theorem choose_permutation {xs ys : List Candidate} (permutation : xs.Perm ys) (floor : Int) :
    choose xs floor = choose ys floor := by
  rw [choose_fold, choose_fold]
  change xs.foldl (pick floor) (decode none) = ys.foldl (pick floor) (decode none)
  rw [fold_decode, fold_decode]
  apply congrArg decode
  apply permutation.foldl_eq'
  intro x _ y _ previous
  exact merge_swap previous (selected floor x) (selected floor y)

end Examples.Proofs.ReferenceDecision

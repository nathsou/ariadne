import Examples.Shallow.unions

namespace Examples.Proofs.ShallowUnions
open Ariadne.Shallow Extracted_unions.Shallow
open NativeTypes

theorem getVersion_valid (version : Int) (id : Ariadne.JSString) :
    getVersion (.valid ⟨version, id⟩) = some version := rfl

theorem getVersion_rejected (reason : Ariadne.JSString) :
    getVersion (.rejected ⟨reason⟩) = none := rfl

theorem copyIfValid_spec (candidate : Candidate) :
    copyIfValid candidate = match candidate with | .valid _ => some candidate | .rejected _ => none := by
  cases candidate <;> rfl

theorem fallback_present (candidate : Candidate) : fallback (some candidate) = candidate := by
  cases candidate <;> rfl

theorem eventValue_changed (value : Int) : eventValue (changed value) = value := rfl

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

end Examples.Proofs.ShallowUnions

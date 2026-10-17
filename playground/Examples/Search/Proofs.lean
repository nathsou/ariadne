import Examples.Search
import Ariadne.Lib.Loop

/-!
# Proofs about binary search

The naive midpoint can leave the safe integers on safe inputs; the careful one cannot, so the search
built on it is safe on every array JavaScript can hold: the loop ends and no index overflows. And
when it answers, it is right: a returned index holds the target, and in a sorted array a present
target is always found.
-/

namespace Examples.Search.Proofs
open Ariadne Examples.Search

/-- Floor division by two, as `omega` understands it. -/
theorem fdiv_two (a : Int) : Int.fdiv a 2 = a / 2 := Int.fdiv_eq_ediv_of_nonneg a (by decide)

/-- **The bug.** Two safe integers, `lo ≤ hi`, on which `(lo + hi) / 2` leaves the safe integers: the
naive midpoint's safety condition fails, so nothing is claimed about its result there. -/
theorem midpointNaive_overflows :
    ∃ lo hi : Int, 0 ≤ lo ∧ lo ≤ hi ∧ inRange lo = true ∧ inRange hi = true ∧ midpointNaive.safe lo hi = false :=
  ⟨2 ^ 52, 2 ^ 52, by decide, by decide, by decide, by decide, by decide⟩

/-- **The fix.** The careful midpoint is safe on every pair of safe integers with `0 ≤ lo ≤ hi`. -/
theorem midpoint_safe (lo hi : Int) (h0 : 0 ≤ lo) (h : lo ≤ hi) (hh : inRange hi = true) :
    midpoint.safe lo hi = true := by
  simp only [inRange, Nat.ble_eq] at hh
  rw [midpoint.safe_iff]
  simp only [inRange, fdiv_two, Nat.ble_eq]
  omega

/-- The midpoint lies in the range, below its end. -/
theorem midpoint_between (lo hi : Int) (h : lo < hi) : lo ≤ midpoint lo hi ∧ midpoint lo hi < hi := by
  simp only [midpoint, fdiv_two]
  omega

/-- The search's loop state, in its definition and in its safety condition: the variables it assigns, `(hi, lo)`. -/
abbrev State := Int × Int

/-- What stays true across iterations: the bounds stay inside the array. -/
def Bounds (xs : List Int) : State → Prop
  | (hi, lo) => 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ xs.length

/-- The distance between the bounds, which every iteration shrinks. -/
def distance : State → Nat
  | (hi, lo) => (hi - lo).toNat

/-- **Safety.** On any array shorter than 2^53 (every JavaScript array), the loop ends and no step
overflows: the distance `hi - lo` shrinks at every iteration. -/
theorem indexOf_safe (xs : List Int) (target : Int) (h : xs.length < 2 ^ 53) :
    indexOf.safe xs target = true := by
  unfold indexOf.safe
  refine whileSafe_of_measure (Bounds xs) distance ?_ (fun _ _ => rfl) _
    ⟨Int.le_refl 0, by simp, Int.le_refl _⟩ (by simp [distance, loopBound]; omega)
  rintro next ex ⟨hi, lo⟩ ⟨h0, hl, hh⟩ hc hn -
  simp only [decide_eq_true_eq] at hc
  have hs := midpoint_safe lo hi h0 (Int.le_of_lt hc) (by simp only [inRange, Nat.ble_eq]; omega)
  have hm := midpoint_between lo hi hc
  simp only [hs, Bool.true_and]
  split
  · rfl
  · split
    · rfl
    · split
      · have hr : inRange (midpoint lo hi + 1) = true := by simp only [inRange, Nat.ble_eq]; omega
        rw [hr, Bool.true_and]
        exact hn _ ⟨by omega, by omega, hh⟩ (by simp only [distance]; omega)
      · exact hn _ ⟨h0, by omega, by omega⟩ (by simp only [distance]; omega)

/-- **Soundness.** A returned index other than -1 holds the target. -/
theorem indexOf_found (xs : List Int) (target : Int) (i : Int) (h : indexOf xs target = i) (hi : i ≠ -1) :
    0 ≤ i ∧ xs[i.toNat]? = some target := by
  subst h
  revert hi
  unfold indexOf
  refine whileDo_inv (Bounds xs) (fun r => r ≠ -1 → 0 ≤ r ∧ xs[r.toNat]? = some target) ?_
    (fun _ _ h => absurd rfl h) ((xs.length : Int), 0) ⟨Int.le_refl 0, by simp, Int.le_refl _⟩
  rintro next ex ⟨hi, lo⟩ ⟨h0, hl, hh⟩ hc hn -
  simp only [decide_eq_true_eq] at hc
  have hm := midpoint_between lo hi hc
  dsimp only [indexOf.loop]
  split
  · intro h; exact absurd rfl h
  · rename_i v hv
    split
    · rename_i he
      simp only [beq_iff_eq] at he
      intro _
      simp only [listIndex, show 0 ≤ midpoint lo hi by omega, ite_true] at hv
      exact ⟨by omega, he ▸ hv⟩
    · split
      · exact hn _ ⟨by omega, by omega, hh⟩
      · exact hn _ ⟨h0, by omega, by omega⟩

/-- Every occurrence of the target lies between the bounds. -/
def Brackets (xs : List Int) (target : Int) : State → Prop
  | (hi, lo) => ∀ k : Nat, xs[k]? = some target → lo ≤ k ∧ (k : Int) < hi

/-- **Completeness.** In a sorted array, a target that is present is found. -/
theorem indexOf_complete (xs : List Int) (target : Int) (sorted : xs.Pairwise (· ≤ ·)) (mem : target ∈ xs)
    (h : xs.length < 2 ^ 53) : indexOf xs target ≠ -1 := by
  unfold indexOf
  refine whileDo_measure (fun s => Bounds xs s ∧ Brackets xs target s) (· ≠ -1) distance ?_ ?_ _
    ⟨⟨Int.le_refl 0, by simp, Int.le_refl _⟩, fun k hk => ?_⟩ (by simp [distance, loopBound]; omega)
  · rintro next ex ⟨hi, lo⟩ ⟨⟨h0, hl, hh⟩, hocc⟩ hc hn -
    simp only [decide_eq_true_eq] at hc
    have hm := midpoint_between lo hi hc
    have hmid : (0 : Int) ≤ midpoint lo hi := by omega
    have hlt : (midpoint lo hi).toNat < xs.length := by omega
    dsimp only [indexOf.loop]
    split
    · rename_i hv
      simp [listIndex, hmid, hlt] at hv
    · rename_i v hv
      simp only [listIndex, hmid, ite_true, List.getElem?_eq_getElem hlt, Option.some.injEq] at hv
      split
      · omega
      · rename_i hne
        simp only [beq_iff_eq] at hne
        split
        · rename_i hvt
          simp only [decide_eq_true_eq] at hvt
          refine hn _ ⟨⟨by omega, by omega, hh⟩, fun k hk => ?_⟩ (by simp only [distance]; omega)
          obtain ⟨hk1, hk2⟩ := hocc k hk
          refine ⟨?_, hk2⟩
          -- Every element up to the midpoint is at most `v`, which is below the target.
          false_or_by_contra
          have hkm : k ≤ (midpoint lo hi).toNat := by omega
          have hkl : k < xs.length := by omega
          rw [List.getElem?_eq_getElem hkl, Option.some.injEq] at hk
          have : xs[k] ≤ xs[(midpoint lo hi).toNat] := by
            rcases Nat.lt_or_eq_of_le hkm with hk' | hk'
            · exact List.pairwise_iff_getElem.mp sorted k _ hkl hlt hk'
            · simp [hk']
          omega
        · rename_i hvt
          simp only [decide_eq_true_eq, Int.not_lt] at hvt
          refine hn _ ⟨⟨h0, by omega, by omega⟩, fun k hk => ?_⟩ (by simp only [distance]; omega)
          obtain ⟨hk1, hk2⟩ := hocc k hk
          refine ⟨hk1, ?_⟩
          -- Every element from the midpoint on is at least `v`, which is above the target.
          false_or_by_contra
          have hkm : (midpoint lo hi).toNat ≤ k := by omega
          have hkl : k < xs.length := by omega
          rw [List.getElem?_eq_getElem hkl, Option.some.injEq] at hk
          have : xs[(midpoint lo hi).toNat] ≤ xs[k] := by
            rcases Nat.lt_or_eq_of_le hkm with hk' | hk'
            · exact List.pairwise_iff_getElem.mp sorted _ k hlt hkl hk'
            · simp [hk']
          omega
  · -- The loop ends with `lo ≥ hi`, but an occurrence would lie between them.
    rintro ⟨hi, lo⟩ ⟨⟨h0, hl, hh⟩, hocc⟩ hc
    simp only [decide_eq_false_iff_not, Int.not_lt] at hc
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp mem
    have := hocc k hk
    omega
  · have := (List.getElem?_eq_some_iff.mp hk).1
    simp only [Int.natCast_nonneg, true_and]
    omega

/-- **The claim about the JavaScript.** Every run of `indexOf(xs, target)` on a JavaScript array of
numbers returns an index: one holding the target, or -1, and in a sorted array -1 only when the
target is absent. -/
theorem indexOf_run (xs : List Int) (target : Int) (vs : List JSValue)
    (args : ArgsRepS names isos sig.indexOf.params vs (xs, target, ())) (h : xs.length < 2 ^ 53) :
    ∃ i : Int, Converges (fun fuel => run ast fuel "indexOf" vs) (.ok (.number i)) ∧
      (i = -1 ∨ (0 ≤ i ∧ xs[i.toNat]? = some target)) ∧
      (xs.Pairwise (· ≤ ·) → target ∈ xs → i ≠ -1) := by
  obtain ⟨w, runs, rep⟩ := indexOf.source xs target vs args (indexOf_safe xs target h)
  simp only [Ty.RepS] at rep
  subst rep
  refine ⟨_, runs, ?_, fun sorted mem => indexOf_complete xs target sorted mem h⟩
  by_cases hi : indexOf xs target = -1
  · exact Or.inl hi
  · exact Or.inr (indexOf_found xs target _ rfl hi)

end Examples.Search.Proofs

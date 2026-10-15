import Tests.Generated.Records
import Tests.Generated.Arrays
import Tests.Generated.Loops
import Ariadne.Lib.Loop
import Ariadne.Lib.Cmp
import Ariadne.Lib.Safe

/-!
# Using the source theorems

A property proved about the readable definitions holds of every run of the
TypeScript functions: here, `choose` with a positive number and no floor returns a
valid choice of that number, even when `floor` is omitted from the call.

For a function whose safety condition is not trivial (numbers), the source
theorem needs the condition: here, `scaled` is safe when its inputs are small.
-/

namespace Tests.Properties
open Ariadne Tests.Generated.Records

theorem orDefault_choose (n : Int) (h : 0 < n) : orDefault (choose n none) = n := by
  simp [orDefault, choose, h]

/-- Calling `choose(n)` in JavaScript (the optional `floor` omitted) returns a value
representing `choose n none`. -/
theorem choose_run (n : Int) :
    ∃ w, Converges (fun fuel => run ast fuel "choose" [.bigint n]) (.ok w) ∧
      Ty.Rep ty.Choice w (choose n none) :=
  choose.source n none [.bigint n] ⟨_, _, rfl, rfl, _, _, rfl, Or.inl rfl, rfl⟩

section
open Tests.Generated.Arrays

/-- Scaling numbers of at most a million by at most a million stays exact. -/
theorem scaled_safe (xs : List Int) (k : Int) (hx : ∀ x ∈ xs, x.natAbs ≤ 1000000) (hk : k.natAbs ≤ 1000000) :
    scaled.safe xs k = true := by
  simp only [scaled.safe, List.all_eq_true, List.mem_filter, inRange, Nat.ble_eq, Int.natAbs_mul]
  intro x ⟨hm, _⟩
  have := Nat.mul_le_mul (hx x hm) hk
  omega

theorem scaled_length (xs : List Int) (k : Int) : (scaled xs k).length ≤ xs.length := by
  simpa [scaled] using List.length_filter_le _ xs

/-- Every run of `scaled` on small inputs returns an array no longer than its input. -/
theorem scaled_run (xs : List Int) (k : Int) (vs : List JSValue)
    (args : ArgsRep sig.scaled.params vs (xs, k, ()))
    (hx : ∀ x ∈ xs, x.natAbs ≤ 1000000) (hk : k.natAbs ≤ 1000000) :
    ∃ w, Converges (fun fuel => run Generated.Arrays.ast fuel "scaled" vs) (.ok w) ∧
      Ty.Rep (.array .number) w (scaled xs k) ∧ (scaled xs k).length ≤ xs.length := by
  obtain ⟨w, hc, hr⟩ := scaled.source xs k vs args (scaled_safe xs k hx hk)
  exact ⟨w, hc, hr, scaled_length xs k⟩

end

section
open Tests.Generated.Loops

/-- The loop in `sum`, from an accumulator. -/
theorem fold_sum (ys : List Int) (acc : Int) : Ariadne.fold acc ys sum.loop = acc + ys.sum := by
  induction ys generalizing acc with
  | nil => simp [Ariadne.fold]
  | cons y ys ih =>
    simp only [Ariadne.fold, List.foldl_cons, sum.loop] at ih ⊢
    rw [ih]; simp [List.sum_cons]; omega

/-- `sum` computes the sum of its array. -/
theorem sum_eq (xs : List Int) : sum xs = xs.sum := by
  simpa [sum] using fold_sum xs 0

/-- `sum`'s loop never leaves early, so its readable definition is a fold, by definition. -/
theorem sum_foldl (xs : List Int) : sum xs = xs.foldl (· + ·) 0 := rfl

/-- `countTagged`'s loop too, though its iterations branch. -/
theorem countTagged_foldl (items : List Item) (tag : JSString) :
    countTagged items tag = items.foldl (fun n it => if it.tags.any (· == tag) then n + 1 else n) 0 := by
  show List.foldl _ 0 items = _
  congr 1
  funext n it
  by_cases h : it.tags.any (· == tag) <;> simp [h, countTagged.loop]

/-- `firstAbove`'s `while` loop ends, and its index stays exact, on arrays shorter than 2^53: the
measure is the number of elements left. -/
theorem firstAbove_safe (xs : List Int) (limit : Int) (h : xs.length < 2 ^ 53) : firstAbove.safe xs limit = true := by
  unfold firstAbove.safe
  refine whileSafe_of_measure (fun s => s.2.1 = xs ∧ 0 ≤ s.1) (fun s => ((xs.length : Int) - s.1).toNat) ?_
    (fun _ _ => rfl) _ ⟨rfl, Int.le_refl 0⟩ (by simp [loopBound]; omega)
  rintro next ex ⟨i, ys, l, ⟨⟩⟩ ⟨rfl, hi⟩ hc hn -
  simp only [decide_eq_true_eq] at hc hi h
  have hr : inRange (i + 1) = true := by simp only [inRange, Nat.ble_eq]; omega
  dsimp only
  split <;> split
  all_goals first
    | rfl
    | rw [hr, Bool.true_and]; exact hn _ ⟨rfl, by omega⟩ (by simp only; omega)

/-- `ranked` sorts by a declared comparator; `cmp_laws` proves it lawful, and `ariadne_safe` discharges
`toSorted`'s safety condition with that. -/
theorem ranked_safe (es : List Generated.Arrays.Entry) : Generated.Arrays.ranked.safe es = true := by
  ariadne_safe [consistent_of_laws (show CmpLaws Generated.Arrays.bySizeDesc by cmp_laws)]

/-- Every run of `sum` on an input where it stays exact returns the sum. -/
theorem sum_run (xs : List Int) (vs : List JSValue) (args : ArgsRep sig.sum.params vs (xs, ()))
    (safe : sum.safe xs = true) :
    ∃ w, Converges (fun fuel => run Generated.Loops.ast fuel "sum" vs) (.ok w) ∧ Ty.Rep .number w xs.sum := by
  obtain ⟨w, hc, hr⟩ := sum.source xs vs args safe
  exact ⟨w, hc, sum_eq xs ▸ hr⟩

end

end Tests.Properties

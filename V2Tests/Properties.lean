import V2Tests.Generated.L1
import V2Tests.Generated.L2

/-!
# Using the source theorems

A property proved about the readable definitions holds of every run of the
TypeScript functions: here, `choose` with a positive number and no floor returns a
valid choice of that number, even when `floor` is omitted from the call.

For a function whose safety condition is not trivial (L2's numbers), the source
theorem needs the condition: here, `scaled` is safe when its inputs are small.
-/

namespace V2Tests.Properties
open V2 V2Tests.Generated.L1

theorem orDefault_choose (n : Int) (h : 0 < n) : «orDefault» («choose» n none) = n := by
  simp [«orDefault», «choose», h]

/-- Calling `choose(n)` in JavaScript (the optional `floor` omitted) returns a value
representing `«choose» n none`. -/
theorem choose_run (n : Int) :
    ∃ w, Converges (fun fuel => run ast fuel "choose" [.bigint n]) (.ok w) ∧
      Ty.Rep ty.«Choice» w («choose» n none) :=
  «choose».source n none [.bigint n] ⟨_, _, rfl, rfl, _, _, rfl, Or.inl rfl, rfl⟩

section
open V2Tests.Generated.L2

/-- Scaling numbers of at most a million by at most a million stays exact. -/
theorem scaled_safe (xs : List Int) (k : Int) (hx : ∀ x ∈ xs, x.natAbs ≤ 1000000) (hk : k.natAbs ≤ 1000000) :
    «scaled».safe xs k = true := by
  simp only [«scaled».safe, List.all_eq_true, List.mem_filter, inRange, Nat.ble_eq, Int.natAbs_mul]
  intro x ⟨hm, _⟩
  have := Nat.mul_le_mul (hx x hm) hk
  omega

theorem scaled_length (xs : List Int) (k : Int) : («scaled» xs k).length ≤ xs.length := by
  simpa [«scaled»] using List.length_filter_le _ xs

/-- Every run of `scaled` on small inputs returns an array no longer than its input. -/
theorem scaled_run (xs : List Int) (k : Int) (vs : List JSValue)
    (args : ArgsRep sig.«scaled».params vs (xs, k, ()))
    (hx : ∀ x ∈ xs, x.natAbs ≤ 1000000) (hk : k.natAbs ≤ 1000000) :
    ∃ w, Converges (fun fuel => run Generated.L2.ast fuel "scaled" vs) (.ok w) ∧
      Ty.Rep (.array .number) w («scaled» xs k) ∧ («scaled» xs k).length ≤ xs.length := by
  obtain ⟨w, hc, hr⟩ := «scaled».source xs k vs args (scaled_safe xs k hx hk)
  exact ⟨w, hc, hr, scaled_length xs k⟩

end

end V2Tests.Properties

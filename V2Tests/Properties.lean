import V2Tests.Generated.L1

/-!
# Using the source theorems

A property proved about the readable definitions holds of every run of the
TypeScript functions: here, `choose` with a positive number and no floor returns a
valid choice of that number, even when `floor` is omitted from the call.
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

end V2Tests.Properties

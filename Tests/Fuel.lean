import Ariadne.Fuel
import Ariadne.Kernel

namespace Tests.Fuel
open Ariadne

/-- A finite timeout never establishes nontermination. -/
example : run { functions := [] } "Number" 0 [.bigint 7] = .error .timeout := rfl
example : run { functions := [] } "Number" 1 [.bigint 7] =
    .ok (.number (Float.Model.ofInt 7)) := by kernel_rfl

/-- A non-timeout fault is stable even when the budget increases. -/
example (fuel : Nat) (enough : 1 ≤ fuel) :
    run { functions := [] } "BigInt" fuel [.number (Float.Model.ofScientific 5 (-1))] =
      .error (.rangeError "BigInt requires a finite integer") := by
  have h := run_fuel_mono { functions := [] } "BigInt"
    [.number (Float.Model.ofScientific 5 (-1))] enough
  have base : run { functions := [] } "BigInt" 1
      [.number (Float.Model.ofScientific 5 (-1))] =
      .error (.rangeError "BigInt requires a finite integer") := by kernel_rfl
  rw [base] at h
  exact (h.eq_of_completed (by intro impossible; cases impossible)).symm

example (evaluate : Nat → Result α) : ¬Converges evaluate (.error .timeout) := by
  rintro ⟨h, _⟩
  exact h rfl

end Tests.Fuel

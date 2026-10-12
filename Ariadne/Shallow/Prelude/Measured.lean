import Ariadne.Shallow.Prelude.Loop

namespace Ariadne.Shallow.Measured

/-- A well-founded loop body decreases its nonnegative measure at every
continuing step; stop and return need no decrease. -/
def run (measure : σ → Nat) (body : σ → Step σ τ)
    (decreases : ∀ s next, body s = .next next → measure next < measure s) (state : σ) : Exit σ τ :=
  match _step : body state with
  | .next next => run measure body decreases next
  | .stop state => .done state
  | .ret value => .ret value
termination_by measure state
decreasing_by exact decreases state next _step

def fuel (body : σ → Step σ τ) : Nat → σ → Option (Exit σ τ)
  | 0, _ => none
  | n + 1, state => match body state with
    | .next next => fuel body n next
    | .stop state => some (.done state)
    | .ret value => some (.ret value)

/-- A budget strictly above the initial measure agrees with well-founded
recursion, independent of the body's choice to stop or return early. -/
theorem fuel_run (measure : σ → Nat) (body : σ → Step σ τ)
    (decreases : ∀ s next, body s = .next next → measure next < measure s)
    (budget : Nat) (state : σ) (enough : measure state < budget) :
    fuel body budget state = some (run measure body decreases state) := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
    rw [run]
    cases step : body state with
    | next next =>
      have smaller := decreases state next step
      simpa only [fuel, step] using ih next (by omega)
    | stop state => simp only [fuel, step]
    | ret value => simp only [fuel, step]

end Ariadne.Shallow.Measured

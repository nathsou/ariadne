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

/-- Iteration for at most `budget` steps. An exhausted budget leaves the loop
in place; a decreasing measure below the budget never reaches that case. -/
def iterate (body : σ → Step σ τ) : Nat → σ → Exit σ τ
  | 0, state => .done state
  | n + 1, state => match body state with
    | .next next => iterate body n next
    | .stop state => .done state
    | .ret value => .ret value

/-- A measured loop's denotation: iteration with one step more than the initial
measure. It is total whatever the body does; `bounded_run` relates it to
well-founded recursion when the measure decreases. -/
def bounded (measure : σ → Int) (init : σ) (body : σ → Step σ τ) : Exit σ τ :=
  iterate body ((measure init).toNat + 1) init

theorem iterate_run (measure : σ → Nat) (body : σ → Step σ τ)
    (decreases : ∀ s next, body s = .next next → measure next < measure s)
    (budget : Nat) (state : σ) (enough : measure state < budget) :
    iterate body budget state = run measure body decreases state := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
    rw [run]
    cases step : body state with
    | next next =>
      have smaller := decreases state next step
      simpa only [iterate, step] using ih next (by omega)
    | stop state => simp only [iterate, step]
    | ret value => simp only [iterate, step]

/-- When every continuing step decreases the measure, the measured loop is the
well-founded recursion on that measure. -/
theorem bounded_run (measure : σ → Int) (init : σ) (body : σ → Step σ τ)
    (decreases : ∀ s next, body s = .next next → (measure next).toNat < (measure s).toNat) :
    bounded measure init body = run (fun s => (measure s).toNat) body decreases init :=
  iterate_run _ body decreases _ init (Nat.lt_succ_self _)

/-- The unfolding equation of a measured loop whose measure decreases. -/
theorem bounded_unfold (measure : σ → Int) (state : σ) (body : σ → Step σ τ)
    (decreases : ∀ s next, body s = .next next → (measure next).toNat < (measure s).toNat) :
    bounded measure state body = match body state with
      | .next next => bounded measure next body
      | .stop state => .done state
      | .ret value => .ret value := by
  rw [bounded_run measure state body decreases, run]
  cases step : body state with
  | next next => exact (bounded_run measure next body decreases).symm
  | stop state => rfl
  | ret value => rfl

end Ariadne.Shallow.Measured

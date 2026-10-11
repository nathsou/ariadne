import Ariadne.Properties

namespace Ariadne

/-- Preservation includes evaluation effects in a loop guard. -/
def GuardPreserves (p : Program) (guard : Expr) (invariant : State → Prop) : Prop :=
  ∀ fuel before value after,
    invariant before → evalExpr p fuel before guard = .ok (value, after) → invariant after

def StmtPreserves (p : Program) (body : Stmt) (invariant : State → Prop) : Prop :=
  ∀ fuel before after,
    invariant before → exec p fuel before body = .ok after → invariant after.state

/-- A loop invariant covers normal exit, break, and return. Continue executes the
update before the next iteration, so its preservation is an explicit premise. -/
theorem loop_preserves (p : Program) (guard : Expr) (body : Stmt)
    (update : Option Stmt) (invariant : State → Prop)
    (guardSafe : GuardPreserves p guard invariant)
    (bodySafe : StmtPreserves p body invariant)
    (updateSafe : ∀ stmt, update = some stmt → StmtPreserves p stmt invariant)
    (fuel : Nat) (before : State) (after : Completion)
    (initial : invariant before)
    (executed : loop p fuel before guard body update = .ok after) : invariant after.state := by
  induction fuel generalizing before after with
  | zero => cases executed
  | succ fuel ih =>
    cases hg : evalExpr p fuel before guard with
    | error err => simp [bind, Except.bind, loop, hg] at executed
    | ok pair =>
      rcases pair with ⟨value, tested⟩
      have testedSafe := guardSafe fuel before value tested initial hg
      by_cases stop : value.truthy = false
      · simp [bind, pure, Except.bind, loop, hg, stop] at executed
        cases executed
        exact testedSafe
      · have go : value.truthy = true := by cases h : value.truthy <;> simp_all
        cases hb : exec p fuel tested body with
        | error err => simp [bind, Except.bind, loop, hg, go, hb] at executed
        | ok out =>
          have outSafe := bodySafe fuel tested out testedSafe hb
          by_cases returned : out.control == .returned
          · simp [bind, pure, Except.bind, loop, hg, go, hb, returned] at executed
            cases executed
            exact outSafe
          · by_cases broke : out.control == .broke
            · simp [bind, pure, Except.bind, loop, hg, go, hb, returned, broke] at executed
              cases executed
              exact outSafe
            · cases update with
              | none =>
                simp [bind, pure, Except.bind, loop, hg, go, hb, returned, broke] at executed
                exact ih out.state after outSafe executed
              | some stmt =>
                cases hu : exec p fuel out.state stmt with
                | error err => simp [bind, Except.bind, Except.map, loop, hg, go, hb, returned, broke, hu] at executed
                | ok updated =>
                  have updatedSafe := updateSafe stmt rfl fuel out.state updated outSafe hu
                  simp [bind, Except.bind, Except.map, loop, hg, go, hb, returned, broke, hu] at executed
                  exact ih updated.state after updatedSafe executed

end Ariadne

import Ariadne.Shallow.Safety.Control
import Ariadne.Convergence

namespace Ariadne.Shallow.Adequacy

private theorem controlBeq (a b : Control) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

/-- The source loop restores its caller's lexical environment after each body,
while retaining heap writes and allocations. -/
def restoreIteration (before : State) (out : Completion) : Completion :=
  { out with state := { out.state with env := before.env } }

def StepRelated (state : State → σ → Prop) (result : State → Value → τ → Prop)
    (before : State) (out : Completion) (step : Step σ τ) : Prop :=
  let restored := restoreIteration before out
  match step with
  | .next next => (out.control = .normal ∨ out.control = .continued) ∧ state restored.state next
  | .stop next => out.control = .broke ∧ state restored.state next
  | .ret value => out.control = .returned ∧ result restored.state out.value value

def ExitRelated (state : State → σ → Prop) (result : State → Value → τ → Prop)
    (out : Completion) (exit : Exit σ τ) : Prop :=
  match exit with
  | .done final => out.control = .normal ∧ state out.state final
  | .ret value => out.control = .returned ∧ result out.state out.value value

/-- Structural source-loop correspondence. The body contract is required only
when its actual guard is true; the safety fold supplies that fact for visited
iterations. There is no fixed body cost, termination bound, or whole-loop
execution assumption in the premises. State relations may include ownership
and disjoint-frame invariants. -/
theorem each_eventually (program : Program) (name : String) (statement : Stmt)
    (body : α → σ → Step σ τ × Bool) (state : State → σ → Prop) (result : State → Value → τ → Prop)
    (values : List (Value × α))
    (bodySpec : ∀ pair ∈ values, ∀ before initial, state before initial → (body pair.2 initial).2 = true →
      ∃ out, Converges (fun fuel => exec program fuel (before.declare name pair.1) statement) (.ok out) ∧
        StepRelated state result before out (body pair.2 initial).1)
    (before : State) (initial : σ) (related : state before initial)
    (safe : (Safety.each (fun pair s => body pair.2 s) values initial).2 = true) :
    ∃ out, ExitRelated state result out (Loop.each values initial (fun pair s => (body pair.2 s).1)) ∧
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        eachBody program fuel before name statement (values.map Prod.fst) = .ok out := by
  induction values generalizing before initial with
  | nil =>
    refine ⟨{ state := before }, ⟨rfl, related⟩, 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons pair rest ih =>
    cases computed : body pair.2 initial with
    | mk step guard =>
      have localSafe : guard = true := by
        cases step <;> simp_all [Safety.each]
      obtain ⟨out, executed, stepRelated⟩ := bodySpec pair (by simp) before initial related
        (by simpa [computed] using localSafe)
      obtain ⟨bodyCost, bodyRuns⟩ :=
        ((converges_iff_eventually _ (fun h => exec_fuel_mono program h _ _) _).mp executed).2
      have restSpec := fun pair member => bodySpec pair (List.mem_cons_of_mem _ member)
      cases step with
      | next next =>
        have nextRelated : (out.control = .normal ∨ out.control = .continued) ∧
            state (restoreIteration before out).state next := by simpa [computed, StepRelated] using stepRelated
        have restSafe : (Safety.each (fun pair s => body pair.2 s) rest next).2 = true := by
          simpa [Safety.each, computed, localSafe] using safe
        obtain ⟨final, finalRelated, restCost, restRuns⟩ :=
          ih restSpec (restoreIteration before out).state next nextRelated.2 restSafe
        refine ⟨final, ?_, max bodyCost restCost + 1, ?_⟩
        · simpa [Loop.each, computed] using finalRelated
        · intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
            have hb := bodyRuns fuel (by omega)
            have ht := restRuns fuel (by omega)
            rcases nextRelated.1 with normal | normal
            all_goals simpa [eachBody, hb, normal, controlBeq, restoreIteration, bind, Except.bind, pure, Except.pure] using ht
      | stop next =>
        have stopped : out.control = .broke ∧ state (restoreIteration before out).state next := by
          simpa [computed, StepRelated] using stepRelated
        refine ⟨{ state := (restoreIteration before out).state }, ?_, bodyCost + 1, ?_⟩
        · simpa [Loop.each, computed, ExitRelated] using stopped.2
        · intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
            simp [eachBody, bodyRuns fuel (by omega), stopped.1, controlBeq, restoreIteration, bind, Except.bind, pure, Except.pure]
      | ret value =>
        have returned : out.control = .returned ∧ result (restoreIteration before out).state out.value value := by
          simpa [computed, StepRelated] using stepRelated
        refine ⟨restoreIteration before out, ?_, bodyCost + 1, ?_⟩
        · simpa [Loop.each, computed, ExitRelated, restoreIteration] using returned
        · intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
            simp [eachBody, bodyRuns fuel (by omega), returned.1, controlBeq, restoreIteration, bind, Except.bind, pure, Except.pure]

theorem forOf_converges (program : Program) (name : String) (statement : Stmt)
    (body : α → σ → Step σ τ × Bool) (state : State → σ → Prop) (result : State → Value → τ → Prop)
    (values : List (Value × α))
    (bodySpec : ∀ pair ∈ values, ∀ before initial, state before initial → (body pair.2 initial).2 = true →
      ∃ out, Converges (fun fuel => exec program fuel (before.declare name pair.1) statement) (.ok out) ∧
        StepRelated state result before out (body pair.2 initial).1)
    (before tested entered : State) (collection : Expr) (source : Value)
    (evaluated : Evaluates program before collection source tested)
    (iterated : iterable tested source = .ok (values.map Prod.fst, entered))
    (initial : σ) (related : state entered initial)
    (safe : (Safety.each (fun pair s => body pair.2 s) values initial).2 = true)
    (mutable : Bool) (span : Span) :
    ∃ out, Converges (fun fuel => exec program fuel before (.forOf mutable name collection statement span)) (.ok out) ∧
      ExitRelated state result out (Loop.each values initial (fun pair s => (body pair.2 s).1)) := by
  obtain ⟨out, represented, loopCost, loopRuns⟩ :=
    each_eventually program name statement body state result values bodySpec entered initial related safe
  obtain ⟨exprCost, exprRuns⟩ := evaluated.eventually
  refine ⟨out, ⟨(by intro h; cases h), max exprCost loopCost + 1, ?_⟩, represented⟩
  simpa [exec, exprRuns _ (Nat.le_max_left ..), iterated, bind, Except.bind]
    using loopRuns _ (Nat.le_max_right exprCost loopCost)

end Ariadne.Shallow.Adequacy

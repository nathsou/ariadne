import Examples.Recursive.forever

namespace Examples.Divergence
open Ariadne
open Recursive_forever (compiled_definitions)

private theorem forever_link (depth fuel : Nat) (external : Target.Runtime) (before : State) :
    Target.link external compiled_definitions depth fuel before (.function "forever") [] =
      .error .timeout := by
  induction depth generalizing fuel before with
  | zero => rfl
  | succ depth ih =>
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    rcases fuel with _ | fuel
    · rfl
    simp only [compiled_definitions] at ih
    simp [Target.link, compiled_definitions, Target.function, Target.scope,
      Target.sequence, Target.return_, Target.call, Target.read, Target.noArgs,
      bind, pure, Except.pure, Except.bind, ih]

/-- This quantifies over every budget. A single timeout alone would not justify
this conclusion about the model's unbounded behavior. -/
theorem forever_exhausts (fuel : Nat) :
    Recursive_forever.compiled_ts_forever fuel [] = .error .timeout := by
  simp [Recursive_forever.compiled_ts_forever, forever_link, Except.map]

theorem forever_does_not_converge (outcome : Result Value) :
    ¬Converges (fun fuel => Recursive_forever.compiled_ts_forever fuel []) outcome := by
  rintro ⟨completed, fuel, observed⟩
  change Recursive_forever.compiled_ts_forever fuel [] = outcome at observed
  rw [forever_exhausts] at observed
  exact completed observed.symm

end Examples.Divergence

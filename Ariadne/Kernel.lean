import Lean

namespace Ariadne

open Lean Meta Elab Tactic

/-- Prove a closed equation by checking `Eq.refl` in the kernel only. The
elaborator's unifier is skipped (it is far slower on large denotations); the
kernel still checks the definitional equality. No axioms, no native code. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasFVar || target.hasMVar then
    throwError "kernel_rfl requires a closed equation"
  let some (_, _, rhs) := target.eq? | throwError "expected an equality"
  let proof ← mkEqRefl rhs
  let name ← withOptions (Elab.async.set · false) <|
    mkAuxLemma [] target proof
  goal.assign (mkConst name)
  replaceMainGoal []

end Ariadne

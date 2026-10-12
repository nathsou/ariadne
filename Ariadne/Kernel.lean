import Lean

namespace Ariadne

open Lean Meta Elab Tactic

/-- Check a closed computation equation directly in the kernel. This avoids
elaborator reduction limits; it does not use native evaluation or add axioms. -/
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

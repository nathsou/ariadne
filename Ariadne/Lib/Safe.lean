import Ariadne.Lib.Sort

/-!
# Discharging safety conditions

A function that can leave what the model covers has a safety condition `«f».safe`, a hypothesis of its
source theorem. Most hold on every input once a few facts are known: a comparator is lawful
(`consistent_of_laws`), a callee's condition holds (its own `_safe` lemma). `ariadne_safe [facts]` proves
`«f».safe x … = true` from them: it unfolds the condition, splits its cases, and closes each by `simp`.

```
theorem put_safe (s : Registers) (ref p : JSString) (e : Placed) : put.safe s ref p e = true := by
  ariadne_safe [consistent_of_laws byString_laws]
```

A condition that bounds numbers, or a loop's, needs its own argument (`inRange`, `forIn_inv`,
`whileSafe_of_measure`); `ariadne_safe` then leaves the goals it could not close.
-/

namespace Ariadne

open Lean Elab Tactic Meta

/-- Unfold the definition at the head of the goal's left-hand side (`«f».safe x …` in `«f».safe x … = true`). -/
elab "unfold_head" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "unfold_head: the goal is not an equation"
  let .const n _ := lhs.getAppFn | throwError "unfold_head: the left-hand side is not an application of a definition"
  replaceMainGoal [← g.deltaTarget (· == n)]

/-- Prove a safety condition `«f».safe x … = true` from the given facts (see the module docs). -/
syntax "ariadne_safe" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ariadne_safe) => `(tactic| ariadne_safe [])
  | `(tactic| ariadne_safe [$ls,*]) => `(tactic|
      (intros
       unfold_head
       try dsimp only
       repeat' split
       all_goals (try simp [$ls,*])))

end Ariadne

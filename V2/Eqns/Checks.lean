import V2.Typed.Denote

/-! Equation lemmas of the statements' well-formedness and triviality checks.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``V2.TStmts.wf, ``V2.TArms.wf, ``V2.TArms.labels, ``V2.TStmts.trivial, ``V2.TArms.trivial] do
    let _ ← getEqnsFor? n

import V2.Typed.Denote

/-! Equation lemmas of the expressions' denotation.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``V2.TExpr.denote, ``V2.TCmp.denote] do
    let _ ← getEqnsFor? n

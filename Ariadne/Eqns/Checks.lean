import Ariadne.Typed.Denote

/-! Equation lemmas of the statements' well-formedness and triviality checks.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``Ariadne.TStmts.wf, ``Ariadne.TArms.wf, ``Ariadne.TArms.labels, ``Ariadne.TStmts.trivial, ``Ariadne.TArms.trivial] do
    let _ ← getEqnsFor? n

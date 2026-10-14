import Ariadne.Typed.Denote

/-! Equation lemmas of the statements' denotation and safety conditions.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``Ariadne.TStmts.denote, ``Ariadne.TArms.denote, ``Ariadne.TArms.first, ``Ariadne.TStmts.safe, ``Ariadne.TArms.safe] do
    let _ ← getEqnsFor? n

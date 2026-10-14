import Ariadne.Typed.Denote

/-! Equation lemmas of erasure.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``Ariadne.TExpr.erase, ``Ariadne.TArgs.erase, ``Ariadne.TElems.erase, ``Ariadne.TEntries.erase, ``Ariadne.TFn.erase,
      ``Ariadne.TCmp.erase, ``Ariadne.TArms.erase] do
    let _ ← getEqnsFor? n

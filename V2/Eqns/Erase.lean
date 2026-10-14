import V2.Typed.Denote

/-! Equation lemmas of erasure.

Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in
that proof's module. For the typed syntax's large definitions this takes seconds each, so they
are derived here, in modules that build in parallel, and the proofs import them. -/

open Lean Meta in
run_meta do
  for n in [``V2.TExpr.erase, ``V2.TArgs.erase, ``V2.TElems.erase, ``V2.TEntries.erase, ``V2.TFn.erase,
      ``V2.TCmp.erase, ``V2.TArms.erase] do
    let _ ← getEqnsFor? n

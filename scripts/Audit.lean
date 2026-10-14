import Ariadne
import Tests

/-! Every theorem, including generated source theorems, rests only on Lean's
standard axioms. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if ["Ariadne", "Tests"].contains name.getRoot.toString && info.isTheorem then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless [``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Audited {count} theorems: only standard Lean logical axioms."

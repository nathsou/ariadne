import Examples
import Tests
import Ariadne.Hoare
import Ariadne.Collections

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let root := name.getRoot
    if ["Ariadne", "Examples", "Example_arithmetic", "Example_control_flow",
        "Example_euclid", "Example_fibonacci", "Example_histogram", "Example_map_keys",
        "Example_numbers", "Example_optionals", "Example_pipelines", "Example_power",
        "Example_records", "Example_search", "Example_sorting", "Example_strings", "Tests"].contains root.toString then
      if info.isTheorem then
        count := count + 1
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Audited {count} theorems: only standard Lean logical axioms."

import Ariadne.Properties
import Examples.Generated.arithmetic
import Examples.Generated.control_flow
import Examples.Generated.euclid
import Examples.Generated.fibonacci
import Examples.Generated.histogram
import Examples.Generated.map_keys
import Examples.Generated.numbers
import Examples.Generated.optionals
import Examples.Generated.pipelines
import Examples.Generated.power
import Examples.Generated.records
import Examples.Generated.search
import Examples.Generated.sorting
import Examples.Generated.strings

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Examples.Proofs
open Ariadne

-- Each theorem below includes successful termination at an explicit fuel bound.
-- These are concrete executions, not universally quantified algorithm proofs.

theorem arbitrary_precision :
    SourceReturns Example_arithmetic.source "demo" [] (.bigint 123456789012345678901234567890) := by
  apply Example_arithmetic.ts_demo_source (fuel := 40)
  kernel_rfl

theorem least_common_multiple :
    SourceReturns Example_euclid.source "demo" [] (.bigint 420) := by
  apply Example_euclid.ts_demo_source (fuel := 100)
  kernel_rfl

theorem fibonacci_twenty :
    SourceReturns Example_fibonacci.source "demo" [] (.bigint 6765) := by
  apply Example_fibonacci.ts_demo_source (fuel := 150)
  kernel_rfl

theorem exponentiation_by_squaring :
    SourceReturns Example_power.source "demo" [] (.bigint 847288609443) := by
  apply Example_power.ts_demo_source (fuel := 100)
  kernel_rfl

theorem binary_search_found :
    SourceReturns Example_search.source "demo" [] (.number (Float.Model.ofNat 5)) := by
  apply Example_search.ts_demo_source (fuel := 100)
  kernel_rfl

theorem map_filter_reduce :
    SourceReturns Example_pipelines.source "demo" [] (.bigint 56) := by
  apply Example_pipelines.ts_demo_source (fuel := 100)
  kernel_rfl

theorem captured_local_mutation :
    SourceReturns Example_pipelines.source "capturedAccumulator" [] (.bigint 210) := by
  apply Example_pipelines.ts_capturedAccumulator_source (fuel := 100)
  kernel_rfl

theorem break_and_continue :
    SourceReturns Example_control_flow.source "demo" [] (.number (Float.Model.ofNat 36)) := by
  apply Example_control_flow.ts_demo_source (fuel := 100)
  kernel_rfl

theorem map_callback_order :
    SourceReturns Example_map_keys.source "countedValues" [] (.bigint 7) := by
  apply Example_map_keys.ts_countedValues_source (fuel := 100)
  kernel_rfl

theorem missing_map_value :
    SourceReturns Example_optionals.source "demo" [] (.bigint 7) := by
  apply Example_optionals.ts_demo_source (fuel := 60)
  kernel_rfl

theorem binary64_rounding :
    SourceReturns Example_numbers.source "rounding" [] (.boolean true) := by
  apply Example_numbers.ts_rounding_source (fuel := 30)
  kernel_rfl

theorem signed_zero_is_observable :
    SourceReturns Example_numbers.source "negativeZero" [] (.number (-Float.Model.inf)) := by
  apply Example_numbers.ts_negativeZero_source (fuel := 30)
  kernel_rfl

theorem utf16_length :
    SourceReturns Example_strings.source "codeUnitLength" [] (.number (Float.Model.ofNat 2)) := by
  apply Example_strings.ts_codeUnitLength_source (fuel := 30)
  kernel_rfl

theorem reverse_preserves_code_units :
    SourceReturns Example_strings.source "demo" [] (.string [55296, 56832, 55357, 65]) := by
  apply Example_strings.ts_demo_source (fuel := 100)
  kernel_rfl

/-- Exact final contents, including duplicate values, of the in-place sorting example. -/
theorem insertion_sort_contents :
    arrayResult (runState Example_sorting.program "demo" 200 []) =
      .ok (([-2, 0, 3, 7, 7, 9] : List Int).map (fun n => .number (Float.Model.ofInt n))) := by
  kernel_rfl

theorem insertion_sort_source :
    SourceReaches Example_sorting.source "demo" [] (fun value state =>
      arrayResult (.ok (value, state)) =
        .ok (([-2, 0, 3, 7, 7, 9] : List Int).map (fun n => .number (Float.Model.ofInt n)))) :=
  Example_sorting.certificate.transfer_reaches (array_reaches insertion_sort_contents)

def histogramEntries : List (Value × Value) :=
  [("a", 5), ("b", 2), ("r", 2), ("c", 1), ("d", 1)].map
    (fun (key, count) => (.string (key.toList.map (fun c => UInt16.ofNat c.toNat)),
      .number (Float.Model.ofNat count)))

theorem histogram_contents :
    mapResult (runState Example_histogram.program "demo" 150 []) = .ok histogramEntries := by
  kernel_rfl

theorem histogram_source :
    SourceReaches Example_histogram.source "demo" [] (fun value state =>
      mapResult (.ok (value, state)) = .ok histogramEntries) :=
  Example_histogram.certificate.transfer_reaches (map_reaches histogram_contents)

def keyEntries : List (Value × Value) :=
  [(.number Float.Model.nan, .string [114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116]),
   (.number (Float.Model.ofNat 2), .string [116, 119, 111]),
   (.number (Float.Model.ofNat 0), .string [114, 101, 105, 110, 115, 101, 114, 116, 101, 100])]

/-- NaN replaces its entry; -0 and +0 share a key; reinsertion moves the key last. -/
theorem same_value_zero_and_insertion_order :
    mapResult (runState Example_map_keys.program "demo" 100 []) = .ok keyEntries := by
  kernel_rfl

theorem map_keys_source :
    SourceReaches Example_map_keys.source "demo" [] (fun value state =>
      mapResult (.ok (value, state)) = .ok keyEntries) :=
  Example_map_keys.certificate.transfer_reaches (map_reaches same_value_zero_and_insertion_order)

/-- Exhausted fuel is explicitly inconclusive; it does not prove divergence. -/
theorem bounded_nontermination_observation :
    Example_control_flow.ts_diverges 30 [] = .error .timeout := by
  kernel_rfl

end Examples.Proofs

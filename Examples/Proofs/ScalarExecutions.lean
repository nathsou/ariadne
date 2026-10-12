import Examples.Compiled.boundedSum
import Examples.Compiled.choose
import Examples.Compiled.factorial
import Examples.Compiled.findUnit
import Examples.Compiled.gcd
import Examples.Compiled.multiply
import Examples.Compiled.numberEdges
import Examples.Compiled.quotient
import Examples.Compiled.reverse
import Examples.Compiled.triangular

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Examples.ScalarExecutions
open Ariadne

-- These are concrete regression theorems. The separate Compiled proof module
-- proves multiplication and its termination bound for arbitrary integer inputs.

theorem boundedSum_execution :
    Compiled_boundedSum.compiled_ts_boundedSum 100 [.bigint 20, .bigint 9] =
      .ok (.bigint 16) := by kernel_rfl

theorem boundedSum_source :
    SourceReturns Compiled_boundedSum.source "boundedSum" [.bigint 20, .bigint 9]
      (.bigint 16) :=
  Compiled_boundedSum.compiled_source boundedSum_execution

theorem choose_execution :
    Compiled_choose.compiled_ts_choose 20 [.boolean true, .undefined] =
      .ok (.string [102, 97, 108, 108, 98, 97, 99, 107]) := by kernel_rfl

theorem choose_source :
    SourceReturns Compiled_choose.source "choose" [.boolean true, .undefined]
      (.string [102, 97, 108, 108, 98, 97, 99, 107]) :=
  Compiled_choose.compiled_source choose_execution

theorem factorial_execution :
    Compiled_factorial.compiled_ts_factorial 80 [.bigint 10] =
      .ok (.bigint 3628800) := by kernel_rfl

theorem factorial_source :
    SourceReturns Compiled_factorial.source "factorial" [.bigint 10]
      (.bigint 3628800) :=
  Compiled_factorial.compiled_source factorial_execution

theorem findUnit_execution :
    Compiled_findUnit.compiled_ts_findUnit 80 [.string [65, 55357, 56832, 66], .string [56832]] =
      .ok (.number (Float.Model.ofNat 2)) := by kernel_rfl

theorem findUnit_source :
    SourceReturns Compiled_findUnit.source "findUnit" [.string [65, 55357, 56832, 66], .string [56832]]
      (.number (Float.Model.ofNat 2)) :=
  Compiled_findUnit.compiled_source findUnit_execution

theorem gcd_execution :
    Compiled_gcd.compiled_ts_gcd 80 [.bigint (-270), .bigint 192] =
      .ok (.bigint 6) := by kernel_rfl

theorem gcd_source :
    SourceReturns Compiled_gcd.source "gcd" [.bigint (-270), .bigint 192]
      (.bigint 6) :=
  Compiled_gcd.compiled_source gcd_execution

theorem multiply_execution :
    Compiled_multiply.compiled_ts_multiply 80 [.bigint (-7), .bigint 13] =
      .ok (.bigint (-91)) := by kernel_rfl

theorem multiply_source :
    SourceReturns Compiled_multiply.source "multiply" [.bigint (-7), .bigint 13]
      (.bigint (-91)) :=
  Compiled_multiply.compiled_source multiply_execution

theorem numberEdges_execution :
    Compiled_numberEdges.compiled_ts_numberEdges 30 [.number (Float.Model.ofNat 0), .number (Float.Model.ofNat 1)] =
      .ok (.number (Float.Model.ofNat 0).neg) := by kernel_rfl

theorem numberEdges_source :
    SourceReturns Compiled_numberEdges.source "numberEdges" [.number (Float.Model.ofNat 0), .number (Float.Model.ofNat 1)]
      (.number (Float.Model.ofNat 0).neg) :=
  Compiled_numberEdges.compiled_source numberEdges_execution

theorem quotient_execution :
    Compiled_quotient.compiled_ts_quotient 20 [.bigint (-7), .bigint 3] =
      .ok (.bigint (-2)) := by kernel_rfl

theorem quotient_source :
    SourceReturns Compiled_quotient.source "quotient" [.bigint (-7), .bigint 3]
      (.bigint (-2)) :=
  Compiled_quotient.compiled_source quotient_execution

theorem reverse_execution :
    Compiled_reverse.compiled_ts_reverse 80 [.string [65, 55357, 56832, 66]] =
      .ok (.string [66, 56832, 55357, 65]) := by kernel_rfl

theorem reverse_source :
    SourceReturns Compiled_reverse.source "reverse" [.string [65, 55357, 56832, 66]]
      (.string [66, 56832, 55357, 65]) :=
  Compiled_reverse.compiled_source reverse_execution

theorem triangular_execution :
    Compiled_triangular.compiled_ts_triangular 100 [.bigint 20] =
      .ok (.bigint 210) := by kernel_rfl

theorem triangular_source :
    SourceReturns Compiled_triangular.source "triangular" [.bigint 20]
      (.bigint 210) :=
  Compiled_triangular.compiled_source triangular_execution

theorem quotient_zero_fault :
    Compiled_quotient.compiled_ts_quotient 20 [.bigint 7, .bigint 0] =
      .error (.rangeError "bigint division by zero") := by kernel_rfl

end Examples.ScalarExecutions

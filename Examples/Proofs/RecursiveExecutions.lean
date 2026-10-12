import Examples.Recursive.parity
import Examples.Recursive.fibonacci
import Examples.Recursive.collatz
import Examples.Recursive.scalars
import Examples.Recursive.ackermann
import Examples.Recursive.localFrames
import Examples.Recursive.shortCircuit
import Examples.Recursive.argumentOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Examples.RecursiveExecutions
open Ariadne

-- Concrete source-linked regression theorems. Recursion.lean separately proves
-- countdown for every integer input, with an explicit termination bound.

theorem parity_execution :
    Recursive_parity.compiled_ts_parity 500 [.bigint 37] =
      .ok (.boolean false) := by kernel_rfl

theorem parity_source :
    SourceReturns Recursive_parity.source "parity" [.bigint 37]
      (.boolean false) :=
  Recursive_parity.compiled_source parity_execution

theorem fibonacci_execution :
    Recursive_fibonacci.compiled_ts_fibonacci 100 [.bigint 8] =
      .ok (.bigint 21) := by kernel_rfl

theorem fibonacci_source :
    SourceReturns Recursive_fibonacci.source "fibonacci" [.bigint 8]
      (.bigint 21) :=
  Recursive_fibonacci.compiled_source fibonacci_execution

theorem collatz_execution :
    Recursive_collatz.compiled_ts_collatz 100 [.bigint 6, .bigint 100] =
      .ok (.bigint 8) := by kernel_rfl

theorem collatz_source :
    SourceReturns Recursive_collatz.source "collatz" [.bigint 6, .bigint 100]
      (.bigint 8) :=
  Recursive_collatz.compiled_source collatz_execution

theorem scalars_execution :
    Recursive_scalars.compiled_ts_scalars 60 [.string [97, 98, 99], .number (Float.Model.ofNat 0)] =
      .ok (.bigint 18) := by kernel_rfl

theorem scalars_source :
    SourceReturns Recursive_scalars.source "scalars" [.string [97, 98, 99], .number (Float.Model.ofNat 0)]
      (.bigint 18) :=
  Recursive_scalars.compiled_source scalars_execution

theorem ackermann_execution :
    Recursive_ackermann.compiled_ts_ackermann 160 [.bigint 2, .bigint 2] =
      .ok (.bigint 7) := by kernel_rfl

theorem ackermann_source :
    SourceReturns Recursive_ackermann.source "ackermann" [.bigint 2, .bigint 2]
      (.bigint 7) :=
  Recursive_ackermann.compiled_source ackermann_execution

theorem localFrames_execution :
    Recursive_localFrames.compiled_ts_localFrames 80 [.bigint 5] =
      .ok (.bigint 30) := by kernel_rfl

theorem localFrames_source :
    SourceReturns Recursive_localFrames.source "localFrames" [.bigint 5]
      (.bigint 30) :=
  Recursive_localFrames.compiled_source localFrames_execution

theorem shortCircuit_execution :
    Recursive_shortCircuit.compiled_ts_shortCircuit 20 [.boolean false] =
      .ok (.boolean false) := by kernel_rfl

theorem shortCircuit_source :
    SourceReturns Recursive_shortCircuit.source "shortCircuit" [.boolean false]
      (.boolean false) :=
  Recursive_shortCircuit.compiled_source shortCircuit_execution

theorem shortCircuit_fault :
    Recursive_shortCircuit.compiled_ts_shortCircuit 30 [.boolean true] =
      .error (.rangeError "bigint division by zero") := by kernel_rfl

theorem division_first :
    Recursive_argumentOrder.compiled_ts_argumentOrder 30 [.boolean false] =
      .error (.rangeError "bigint division by zero") := by kernel_rfl

theorem conversion_first :
    Recursive_argumentOrder.compiled_ts_argumentOrder 30 [.boolean true] =
      .error (.rangeError "BigInt requires a finite integer") := by kernel_rfl

end Examples.RecursiveExecutions

import Examples.Generated.arithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Examples.Proofs
open Ariadne Example_arithmetic

/-- A readable functional specification, connected to the parsed TypeScript below. -/
def absolute (x : Int) : Int := if x < 0 then -x else x

def maximum (x y : Int) : Int := if x < y then y else x

def clamp (x low high : Int) : Int := if x < low then low else if x > high then high else x

theorem absolute_model (x : Int) :
    ts_absolute 12 [.bigint x] = .ok (.bigint (absolute x)) := by
  by_cases hx : x < 0
  all_goals simp [ts_absolute, run, runState, apply, callBody, program,
    exec, execBlock, evalExpr, State.declare, State.alloc, State.lookup,
    Value.ofLiteral, Value.truthy, binary, unary, absolute, hx, Except.map]
  all_goals rfl

theorem maximum_model (x y : Int) :
    ts_maximum 12 [.bigint x, .bigint y] = .ok (.bigint (maximum x y)) := by
  by_cases h : x < y
  all_goals simp [ts_maximum, run, runState, apply, callBody, program,
    exec, execBlock, evalExpr, State.declare, State.alloc, State.lookup,
    Value.truthy, binary, maximum, h, Except.map]
  all_goals rfl

theorem clamp_model (x low high : Int) :
    ts_clamp 16 [.bigint x, .bigint low, .bigint high] = .ok (.bigint (clamp x low high)) := by
  by_cases hlo : x < low <;> by_cases hhi : x > high
  all_goals simp [ts_clamp, run, runState, apply, callBody, program,
    exec, execBlock, evalExpr, State.declare, State.alloc, State.lookup,
    Value.truthy, binary, clamp, hlo, hhi, Except.map]
  all_goals rfl

theorem absolute_nonnegative (x : Int) : 0 ≤ absolute x := by
  unfold absolute
  split <;> omega

theorem absolute_source (x : Int) :
    SourceReturns source "absolute" [.bigint x] (.bigint (absolute x)) :=
  ts_absolute_source (absolute_model x)

theorem absolute_source_nonnegative (x : Int) :
    ∃ result, SourceReturns source "absolute" [.bigint x] (.bigint result) ∧ 0 ≤ result :=
  ⟨absolute x, absolute_source x, absolute_nonnegative x⟩

theorem maximum_source_bounds (x y : Int) :
    ∃ result, SourceReturns source "maximum" [.bigint x, .bigint y] (.bigint result) ∧
      x ≤ result ∧ y ≤ result := by
  refine ⟨maximum x y, ts_maximum_source (maximum_model x y), ?_⟩
  unfold maximum
  split <;> omega

theorem clamp_source_bounds (x low high : Int) (ordered : low ≤ high) :
    ∃ result, SourceReturns source "clamp" [.bigint x, .bigint low, .bigint high] (.bigint result) ∧
      low ≤ result ∧ result ≤ high := by
  refine ⟨clamp x low high, ts_clamp_source (clamp_model x low high), ?_⟩
  unfold clamp
  split
  · omega
  · split <;> omega

theorem clamp_source_identity (x low high : Int) (lower : low ≤ x) (upper : x ≤ high) :
    SourceReturns source "clamp" [.bigint x, .bigint low, .bigint high] (.bigint x) := by
  have h : clamp x low high = x := by simp [clamp]; omega
  simpa [h] using ts_clamp_source (clamp_model x low high)

end Examples.Proofs

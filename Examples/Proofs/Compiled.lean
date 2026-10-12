import Examples.Compiled.multiply

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Examples.CompiledProofs
open Ariadne

private def guard : Target.Expression :=
  Target.binary ">" (Target.read "count") (Target.literal (.bigint 0))

private def body : Target.Command :=
  Target.scope (Target.sequence
    (Target.assign "total" (Target.binary "+" (Target.read "total") (Target.read "value")))
    (Target.sequence
      (Target.assign "count" (Target.binary "-" (Target.read "count") (Target.literal (.bigint 1))))
      Target.empty))

private def frame (value count total : Int) : State := {
  env := [("total", 2), ("count", 1), ("value", 0)]
  heap := [.cell (.bigint value), .cell (.bigint count), .cell (.bigint total)] }

/-- A functional specification with no fuel, heap, or source syntax. -/
def multiply (value count : Int) : Int := value * max count 0

private theorem loop_multiply (count : Nat) (value total : Int) :
    Target.loop guard body none (count + 10) (frame value count total) =
      .ok { state := frame value 0 (total + value * count) } := by
  induction count generalizing total with
  | zero =>
    simp [Target.loop, guard, Target.binary, Target.read, Target.literal,
      frame, State.lookup, Value.ofLiteral, binary, Value.truthy, bind, pure, Except.pure, Except.bind]
  | succ count ih =>
    have positive : (0 : Int) < (count : Int) + 1 := by omega
    rw [Target.loop]
    simp [guard, body, Target.binary, Target.read, Target.literal,
      Target.scope, Target.sequence, Target.assign, Target.empty,
      frame, State.lookup, State.assign, State.write, Value.ofLiteral, binary,
      Value.truthy, bind, pure, Except.pure, Except.bind, positive, bne, BEq.beq, instBEqControl.beq]
    change Target.loop guard body none (count + 10) (frame value count (total + value)) = _
    rw [ih]
    congr 3
    simp [Int.mul_add]
    omega

/-- The bound grows with the number of loop iterations, rather than fixing an
example input or using a timeout as a termination argument. -/
theorem multiply_nat (value : Int) (count : Nat) :
    Compiled_multiply.compiled_ts_multiply (count + 16) [.bigint value, .bigint count] =
      .ok (.bigint (value * count)) := by
  have executed := loop_multiply count value 0
  simp only [guard, body, frame, Int.zero_add] at executed
  simp [Compiled_multiply.compiled_ts_multiply, Target.function,
    Target.scope, Target.sequence, Target.declare, Target.while_, Target.literal,
    Target.return_, Target.read, Target.empty, State.declare, State.alloc,
    State.lookup, Value.ofLiteral, bind, pure, Except.pure, Except.bind, Except.map,
    bne, BEq.beq, instBEqControl.beq, executed]
  rfl

theorem multiply_correct (value count : Int) :
    Compiled_multiply.compiled_ts_multiply (count.toNat + 16) [.bigint value, .bigint count] =
      .ok (.bigint (multiply value count)) := by
  cases count with
  | ofNat n =>
    simpa [multiply, Int.max_eq_left (Int.natCast_nonneg n)] using multiply_nat value n
  | negSucc n =>
    have nonpositive : Int.negSucc n ≤ 0 := by omega
    simp [multiply, Int.max_eq_right nonpositive,
      Compiled_multiply.compiled_ts_multiply, Target.function, Target.scope,
      Target.sequence, Target.declare, Target.while_, Target.loop, Target.binary,
      Target.literal, Target.return_, Target.read, Target.empty, State.declare,
      State.alloc, State.lookup, Value.ofLiteral, Value.truthy, binary, bind, pure,
      Except.pure, Except.bind, Except.map, bne, BEq.beq, instBEqControl.beq]
    rfl

/-- End-to-end: exact TypeScript source, arbitrary integers, and termination. -/
theorem multiply_source (value count : Int) :
    SourceReturns Compiled_multiply.source "multiply" [.bigint value, .bigint count]
      (.bigint (multiply value count)) :=
  Compiled_multiply.compiled_source (multiply_correct value count)

/-- A verified bound can be increased without changing the result. -/
theorem multiply_larger_budget (value count : Int) (fuel : Nat)
    (enough : count.toNat + 16 ≤ fuel) :
    Compiled_multiply.compiled_ts_multiply fuel [.bigint value, .bigint count] =
      .ok (.bigint (multiply value count)) := by
  have stable := run_fuel_mono Compiled_multiply.program "multiply"
    [.bigint value, .bigint count] enough
  change (Compiled_multiply.ts_multiply _ _).Refines (Compiled_multiply.ts_multiply _ _) at stable
  rw [← Compiled_multiply.compiled_correct, multiply_correct] at stable
  exact (stable.eq_of_completed (by intro h; cases h)).symm

/-- Every successful modeled execution has the specified result. -/
theorem multiply_unique_result (value count : Int) (result : Value)
    (h : SourceReturns Compiled_multiply.source "multiply" [.bigint value, .bigint count] result) :
    result = .bigint (multiply value count) :=
  h.deterministic (multiply_source value count)

end Examples.CompiledProofs

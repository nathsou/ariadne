import Examples.Shallow.int53

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Examples.Proofs.ShallowInt53
open Extracted_int53.Shallow

theorem add_equation (a b : Int) : add a b = a + b := rfl
theorem multiply_equation (a b : Int) : multiply a b = a * b := rfl
theorem negate_equation (a : Int) : negate a = -a := rfl
theorem remainder_equation (a b : Int) : remainder a b = Int.tmod a b := rfl
theorem floor_equation (a b : Int) : floorDivide a b = Int.fdiv a b := rfl
theorem trunc_equation (a b : Int) : truncDivide a b = Int.tdiv a b := rfl
theorem length_equation (values : List Int) : count values = values.length := rfl

theorem skipped_branch_safe : chooseBranch.safe 9007199254740991 false := by
  constructor <;> kernel_rfl

theorem short_circuit_safe : firstZero.safe [0, 9007199254740991] := by
  constructor <;> kernel_rfl

theorem overflow_rejected : ¬ add.safe 9007199254740991 1 := by decide

theorem signed_zero_rejected : ¬ multiply.safe (-1) 0 := by decide

theorem zero_divisor_rejected : ¬ truncDivide.safe 1 0 := by decide

theorem executed_callback_rejected : ¬ firstZero.safe [9007199254740991, 0] := by decide

end Examples.Proofs.ShallowInt53

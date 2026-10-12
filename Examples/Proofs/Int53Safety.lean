import Examples.Shallow.int53
import Ariadne.Shallow.Prelude.Int53Exact
namespace Examples.Proofs.Int53Safety
open Ariadne Ariadne.Shallow Extracted_int53.Shallow
set_option maxRecDepth 10000

theorem add_safe (a b : Int) (ha : Int53.InRange a) (hb : Int53.InRange b) (sum : Int53.InRange (a + b)) :
    add.safe a b := by
  simp [add.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.add,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.add_exact a b ha hb sum, ha, hb, sum]

theorem multiply_safe (a b : Int) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (product : Int53.InRange (a * b)) (canonical : Int53.CanonicalProduct a b) : multiply.safe a b := by
  simp [multiply.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.multiply,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.mul_exact a b ha hb product canonical, ha, hb, product]

theorem negate_safe (a : Int) (ha : Int53.InRange a) (nonzero : a ≠ 0) : negate.safe a := by
  have hn := Int53.neg_inRange ha
  simp [negate.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.negate,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.neg_exact a ha nonzero, ha, hn]

theorem remainder_safe (a b : Int) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalRemainder a b) : remainder.safe a b := by
  have hr := Int53.remainder_range a b ha
  simp [remainder.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.remainder,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.remainder_exact a b ha hb nonzero canonical, ha, hb, hr, nonzero]
theorem truncDivide_safe (a b : Int) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalTruncQuotient a b) : truncDivide.safe a b := by
  have hr := Int53.tdiv_range a b ha
  simp [truncDivide.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.truncDivide,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.trunc_div_exact a b ha hb nonzero canonical, ha, hb, hr, nonzero]

theorem floorDivide_safe (a b : Int) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalFloorQuotient a b) : floorDivide.safe a b := by
  have hr := Int53.fdiv_range a b ha
  simp [floorDivide.safe, Safety.function, Safety.validEnvironment, Safety.liftEnvironment, CoreArtifacts.floorDivide,
    Safety.term, Safety.getVariable, Safety.valid, Safety.unary, Safety.unarySafe, Safety.binary,
    Safety.binarySafe, Int53.inRange, Int53.floor_div_exact a b ha hb nonzero canonical, ha, hb, hr, nonzero]
end Examples.Proofs.Int53Safety

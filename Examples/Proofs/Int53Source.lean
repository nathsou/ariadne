import Examples.Proofs.Int53Safety
namespace Examples.Proofs.Int53Source
open Ariadne Ariadne.Shallow Extracted_int53.Shallow

-- Arithmetic hypotheses discharge the computed guards before source transfer.
-- Neither a fuel budget nor an operational execution premise is required.
theorem addition (a b : Int) (heap : Heap) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (sum : Int53.InRange (a + b)) :
    SourceReturnsFrom Extracted_int53.source "add" heap
      [.number (Float.Model.ofInt a), .number (Float.Model.ofInt b)]
      (.number (Float.Model.ofInt (a + b))) :=
  add_source a b heap (Int53Safety.add_safe a b ha hb sum)

theorem multiplication (a b : Int) (heap : Heap) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (product : Int53.InRange (a * b)) (canonical : Int53.CanonicalProduct a b) :
    SourceReturnsFrom Extracted_int53.source "multiply" heap
      [.number (Float.Model.ofInt a), .number (Float.Model.ofInt b)]
      (.number (Float.Model.ofInt (a * b))) :=
  multiply_source a b heap (Int53Safety.multiply_safe a b ha hb product canonical)

theorem negation (a : Int) (heap : Heap) (ha : Int53.InRange a) (nonzero : a ≠ 0) :
    SourceReturnsFrom Extracted_int53.source "negate" heap [.number (Float.Model.ofInt a)]
      (.number (Float.Model.ofInt (-a))) :=
  negate_source a heap (Int53Safety.negate_safe a ha nonzero)

theorem remainder (a b : Int) (heap : Heap) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalRemainder a b) :
    SourceReturnsFrom Extracted_int53.source "remainder" heap
      [.number (Float.Model.ofInt a), .number (Float.Model.ofInt b)]
      (.number (Float.Model.ofInt (a.tmod b))) :=
  remainder_source a b heap (Int53Safety.remainder_safe a b ha hb nonzero canonical)

theorem truncated_quotient (a b : Int) (heap : Heap) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalTruncQuotient a b) :
    SourceReturnsFrom Extracted_int53.source "truncDivide" heap
      [.number (Float.Model.ofInt a), .number (Float.Model.ofInt b)]
      (.number (Float.Model.ofInt (a.tdiv b))) :=
  truncDivide_source a b heap (Int53Safety.truncDivide_safe a b ha hb nonzero canonical)

theorem floored_quotient (a b : Int) (heap : Heap) (ha : Int53.InRange a) (hb : Int53.InRange b)
    (nonzero : b ≠ 0) (canonical : Int53.CanonicalFloorQuotient a b) :
    SourceReturnsFrom Extracted_int53.source "floorDivide" heap
      [.number (Float.Model.ofInt a), .number (Float.Model.ofInt b)]
      (.number (Float.Model.ofInt (a.fdiv b))) :=
  floorDivide_source a b heap (Int53Safety.floorDivide_safe a b ha hb nonzero canonical)

end Examples.Proofs.Int53Source

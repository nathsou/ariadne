import Examples.Shallow.source

namespace Examples.Proofs.SourceTransfer
open Ariadne
open Extracted_source.Shallow

/-- A native algebraic fact transfers to the original TypeScript function for
every integer and every initial heap, without an execution-budget assumption. -/
theorem arithmetic_diagonal (x : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "arithmetic" heap [.bigint x, .bigint x] (.bigint 0) := by
  simpa [arithmetic] using arithmetic_source x x heap

/-- The source name `choice_source` remains available; the colliding generated
theorem for `choice` is kept under `SourceChecks.choice.source`. -/
theorem choice_left (x y : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "choice" heap [.boolean true, .bigint x, .bigint y] (.bigint x) := by
  simpa [choice] using SourceChecks.choice.source true x y heap

theorem conjunction_short_circuit (b : Bool) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "conjunction" heap [.boolean false, .boolean b] (.boolean false) := by
  simpa [conjunction] using conjunction_source false b heap

theorem disjunction_short_circuit (b : Bool) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "disjunction" heap [.boolean true, .boolean b] (.boolean true) := by
  simpa [disjunction] using disjunction_source true b heap

end Examples.Proofs.SourceTransfer

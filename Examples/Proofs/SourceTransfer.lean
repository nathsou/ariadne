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

theorem local_cancel (a : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "local" heap [.bigint a, .bigint (-a)] (.bigint 0) := by
  simpa [Extracted_source.Shallow.local, show a + -a = 0 by omega] using local_source a (-a) heap

theorem early_nonnegative (value : Int) (nonnegative : 0 ≤ value) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "early" heap [.bigint value] (.bigint value) := by
  simpa [early, show ¬ value < 0 by omega] using early_source value heap

theorem branch_local_diagonal (a : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "branchLocal" heap [.boolean false, .bigint a, .bigint a] (.bigint 0) := by
  simpa [branchLocal] using branchLocal_source false a a heap

theorem nested_skips_inner (other : Bool) (value : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_source.source "nested" heap [.boolean false, .boolean other, .bigint value] (.bigint 0) := by
  simpa [nested] using nested_source false other value heap

end Examples.Proofs.SourceTransfer

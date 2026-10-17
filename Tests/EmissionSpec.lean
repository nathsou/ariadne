import Tests.Generated.Emission
import Ariadne.Front.Emit

namespace Tests.EmissionSpec
open Ariadne Tests.Generated.Emission

example : marker = js "⟦⟦99⟧⟧ne.«fake».«binding»⟦⟦/⟧⟧" := rfl

example : nested [1, 2] [3, 4] 5 = 40 := by decide

example : keywordNames 2 3 = 5 := rfl

/-- The redundant literal and repeated range checks disappear from the proof interface. -/
example (lo hi : Int) : midpoint.safe lo hi = true ↔ inRange (lo + hi) = true :=
  midpoint.safe_iff lo hi

/-- The simplifier must preserve the overflow obligation. -/
example : midpoint.safe (2 ^ 52) (2 ^ 52) = false := by decide

open Ariadne.Front in
example : (Code.emit "f" (.text "⟦⟦1⟧⟧ordinary text⟦⟦/⟧⟧")).2 = [] := rfl

end Tests.EmissionSpec

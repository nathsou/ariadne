import Quickstart.Spec
import Ariadne.Lib.Loop

/-! # The claims of `Quickstart/Spec.lean`, proved -/

namespace Quickstart.Proofs

open Ariadne Quickstart.Ledger Quickstart.Spec

/-- The loop is a fold; its invariant (`fold_inv`): the running total is non-negative. -/
theorem balance_nonneg : Spec.balance_nonneg := by
  intro entries h
  unfold balance
  dsimp only
  refine fold_inv (fun (t : Int) => 0 ≤ t) entries ?_ _ (Int.le_refl 0)
  intro t e he ht
  have ha : 0 ≤ amount e := h e he
  rcases e with ⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩ <;> dsimp only
  · simp only [amount] at ha; omega
  · by_cases hd : a ≤ t <;> simp [hd] <;> omega

/-- The generated frame lemma: `freeze` never writes `balances`. -/
theorem freeze_keeps_balances : Spec.freeze_keeps_balances :=
  fun a id => freeze.keeps.balances a id

theorem credit_frozen : Spec.credit_frozen := by
  intro a id amount h
  simp [credit, h]

/-- `freeze` has no operation that can leave the model, so its source theorem needs no hypothesis. -/
theorem freeze_runs : Spec.freeze_runs :=
  fun a id this' vs args => freeze.source a id this' vs args

end Quickstart.Proofs

import Quickstart.Spec
import Ariadne.Lib.Loop

/-! # The claims of `Quickstart/Spec.lean`, proved -/

namespace Quickstart.Proofs

open Ariadne Quickstart.Ledger Quickstart.Spec

/-- The loop's invariant: the running total is non-negative. -/
theorem balance_nonneg : Spec.balance_nonneg := by
  intro entries h
  unfold balance
  refine forIn_prefix (fun _ (s : Int × List Entry × Unit) => 0 ≤ s.1) (fun r => 0 ≤ r) entries ?_
    (fun s hs => hs) _ (Int.le_refl 0)
  rintro pre e post next ex ⟨t, es, ⟨⟩⟩ he ht hn
  have ha : 0 ≤ amount e := h e (by simp [he])
  dsimp only at ht ⊢
  rcases e with ⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩
  · exact hn _ (by simp only [amount] at ha; dsimp only; omega)
  · dsimp only
    split
    · rename_i hd
      simp only [decide_eq_true_eq] at hd
      exact hn _ (by dsimp only; omega)
    · exact hn _ ht

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

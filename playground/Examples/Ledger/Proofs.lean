import Examples.Ledger
import Ariadne.Lib.Loop
import Ariadne.Lib.Map

/-!
# Proofs about the ledger

The example of [the guide](https://github.com/nathsou/ariadne/blob/main/docs/GUIDE.md). A union of
records becomes a Lean sum with named constructors (`Entry.credit`), a class becomes a record of its
maps, and each method a function from the old state to the new one.
-/

namespace Examples.Ledger.Proofs
open Ariadne Examples.Ledger

/-- An entry's amount. -/
def amount : Entry → Int
  | .inl (a, ()) | .inr (a, ()) => a

/-- With non-negative amounts, the balance is never negative: a debit larger than the balance is
refused. The loop is a fold; its invariant (`fold_inv`) is that the running total is non-negative. -/
theorem balance_nonneg (entries : List Entry) (h : ∀ e ∈ entries, 0 ≤ amount e) : 0 ≤ balance entries := by
  unfold balance
  dsimp only
  refine fold_inv (fun (t : Int) => 0 ≤ t) entries ?_ _ (Int.le_refl 0)
  intro t e he ht
  have ha : 0 ≤ amount e := h e he
  rcases e with ⟨a, ⟨⟩⟩ | ⟨a, ⟨⟩⟩ <;> dsimp only
  · simp only [amount] at ha; omega
  · by_cases hd : a ≤ t <;> simp [hd] <;> omega

/-- A credit to an account that is not frozen adds the amount to its balance. -/
theorem credit_adds (a : Accounts) (id : JSString) (n : Int) (hf : mapGet a.frozen id = none) (hn : 0 < n) :
    balanceOf (credit a id n) id = balanceOf a id + n := by
  have : ¬n ≤ 0 := by omega
  simp [credit, balanceOf, hf, this, mapGet_mapPut, readable]

/-- A credit changes no other account's balance. -/
theorem credit_other (a : Accounts) (id other : JSString) (n : Int) (h : other ≠ id) :
    balanceOf (credit a id n) other = balanceOf a other := by
  unfold credit
  split
  · rfl
  · simp [balanceOf, mapGet_mapPut, h, readable]

/-- A frozen account takes no credit: the state is unchanged. -/
theorem credit_frozen (a : Accounts) (id : JSString) (n : Int) (h : (mapGet a.frozen id).isSome) :
    credit a id n = a := by
  simp [credit, h]

/-- Freezing changes no balance. The generated frame lemma `freeze.keeps.balances` says so; the
translator emits one for every method and every field it never writes. -/
theorem freeze_keeps_balances (a : Accounts) (id : JSString) : (freeze a id).balances = a.balances :=
  freeze.keeps.balances a id

/-- Freezing is final: a credit after a freeze changes nothing. -/
theorem credit_after_freeze (a : Accounts) (id : JSString) (n : Int) :
    credit (freeze a id) id n = freeze a id :=
  credit_frozen _ _ _ (by simp [freeze, mapGet_mapPut, readable])

/-- A fresh ledger holds nothing. -/
theorem balanceOf_new (id : JSString) : balanceOf «new Accounts» id = 0 := rfl

/-- **The claim about the JavaScript.** Every run of `freeze` on a state and an id representing its
inputs converges to the state the definition gives, so the statements above hold of the TypeScript
method. -/
theorem freeze_runs (a : Accounts) (id : JSString) (this' : JSValue) (vs : List JSValue)
    (args : ArgsRep sig.freeze.params (this' :: vs) (a, id, ())) :
    ∃ w t, Converges (fun fuel => runMethod ast fuel "freeze" this' vs) (.ok (w, t)) ∧
      Ty.Rep ty.Accounts t (freeze a id) :=
  freeze.source a id this' vs args

end Examples.Ledger.Proofs

import Quickstart.Ledger

/-!
# What is claimed of `src/ledger.ts`

Each proposition here is proved by the theorem of the same name in `Quickstart/Proofs.lean`;
`lake exe audit` checks it, and `spec.lock` records these statements.
-/

namespace Quickstart.Spec

open Ariadne Quickstart.Ledger

/-- An entry's amount. -/
def amount : Entry → Int
  | .inl (a, ()) | .inr (a, ()) => a

/-- With non-negative amounts, the balance is never negative: a debit larger than the balance is refused. -/
def balance_nonneg : Prop :=
  ∀ entries : List Entry, (∀ e ∈ entries, 0 ≤ amount e) → 0 ≤ balance entries

/-- Freezing an account changes no balance. -/
def freeze_keeps_balances : Prop :=
  ∀ (a : Accounts) (id : JSString), (freeze a id).balances = a.balances

/-- A frozen account takes no credit. -/
def credit_frozen : Prop :=
  ∀ (a : Accounts) (id : JSString) (amount : Int), (mapGet a.frozen id).isSome → credit a id amount = a

/-- Every run of `freeze`, on a state and an id representing its inputs, converges to the state the
definition gives (so the two statements above hold of the TypeScript). -/
def freeze_runs : Prop :=
  ∀ (a : Accounts) (id : JSString) (this' : JSValue) (vs : List JSValue),
    ArgsRep sig.freeze.params (this' :: vs) (a, id, ()) →
    ∃ w t, Converges (fun fuel => runMethod ast fuel "freeze" this' vs) (.ok (w, t)) ∧
      Ty.Rep ty.Accounts t (freeze a id)

end Quickstart.Spec

import Ariadne.Typed.Denote

/-!
# Loops

Readable definitions run loops through `Ariadne.forIn items step exit s`: `step y next exit s` handles one
item, continuing with `next` or leaving with `exit`. These lemmas reason about such loops with an
invariant, as a `for` loop's correctness is usually argued.
-/

namespace Ariadne

theorem forIn_nil {α σ R : Type} (step : α → (σ → R) → (σ → R) → σ → R) (exit : σ → R) (s : σ) :
    forIn [] step exit s = exit s := rfl

theorem forIn_cons {α σ R : Type} (y : α) (ys : List α) (step : α → (σ → R) → (σ → R) → σ → R)
    (exit : σ → R) (s : σ) : forIn (y :: ys) step exit s = step y (forIn ys step exit) exit s := rfl

/-- An invariant of a loop: if every iteration, from a state satisfying `P`, ends in `Q` provided continuing
and leaving do, and leaving from `P` ends in `Q`, then the loop does. -/
theorem forIn_inv {α σ R : Type} (P : σ → Prop) (Q : R → Prop) {step : α → (σ → R) → (σ → R) → σ → R}
    {exit : σ → R}
    (hstep : ∀ y next ex s, P s → (∀ s', P s' → Q (next s')) → (∀ s', P s' → Q (ex s')) → Q (step y next ex s))
    (hexit : ∀ s, P s → Q (exit s)) : ∀ (items : List α) s, P s → Q (forIn items step exit s)
  | [], s, h => hexit s h
  | y :: ys, s, h => hstep y _ exit s h (fun s' h' => forIn_inv P Q hstep hexit ys s' h') hexit

/-- An invariant over the items processed so far: if, from a state satisfying `P` after the items `pre`,
an iteration on `y` ends in `Q` provided continuing after `pre ++ [y]` does, and leaving after all the items
ends in `Q`, then the loop does. (For loops that never leave early.) -/
theorem forIn_prefix {α σ R : Type} (P : List α → σ → Prop) (Q : R → Prop) {step : α → (σ → R) → (σ → R) → σ → R}
    {exit : σ → R} (items : List α)
    (hstep : ∀ pre y post next ex s, items = pre ++ y :: post → P pre s → (∀ s', P (pre ++ [y]) s' → Q (next s')) →
      Q (step y next ex s))
    (hexit : ∀ s, P items s → Q (exit s)) : ∀ s, P [] s → Q (forIn items step exit s) := by
  suffices h : ∀ post pre s, items = pre ++ post → P pre s → Q (forIn post step exit s) from
    fun s hs => h items [] s rfl hs
  intro post
  induction post with
  | nil => intro pre s he hs; simp at he; subst he; exact hexit s hs
  | cons y ys ih =>
    intro pre s he hs
    exact hstep pre y ys _ exit s he hs fun s' hs' => ih (pre ++ [y]) s' (by simp [he]) hs'

end Ariadne

import Ariadne.Typed.Denote
import Ariadne.Typed.Direct

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

/-- An invariant of a fold (how a readable definition writes a loop that runs every iteration): what every
step keeps, on the items, holds after all of them. -/
theorem fold_inv {α σ : Type} (P : σ → Prop) {step : σ → α → σ} :
    ∀ (items : List α), (∀ s y, y ∈ items → P s → P (step s y)) → ∀ (s : σ), P s → P (fold s items step)
  | [], _, _, h => h
  | y :: ys, hstep, s, h =>
    fold_inv P ys (fun s' y' hy => hstep s' y' (List.mem_cons_of_mem y hy)) (step s y)
      (hstep s y List.mem_cons_self h)

/-- An invariant of `Ariadne.fold` over the items processed so far (the fold's `forIn_prefix`): each step knows where
it is in the list. -/
theorem fold_prefix {α σ : Type} (P : List α → σ → Prop) {step : σ → α → σ} (items : List α)
    (hstep : ∀ pre y post s, items = pre ++ y :: post → P pre s → P (pre ++ [y]) (step s y)) :
    ∀ s, P [] s → P items (fold s items step) := by
  suffices h : ∀ post pre s, items = pre ++ post → P pre s → P items (post.foldl step s) from
    fun s hs => h items [] s rfl hs
  intro post
  induction post with
  | nil => intro pre s he hs; simp at he; subst he; exact hs
  | cons y ys ih => intro pre s he hs; exact ih (pre ++ [y]) _ (by simp [he]) (hstep pre y ys s he hs)

/-- A fold computes `g items` when its start is `g []` and each step takes `g pre` to `g (pre ++ [y])`. -/
theorem fold_eq {α σ : Type} (g : List α → σ) {step : σ → α → σ} {init : σ} (h0 : init = g [])
    (hstep : ∀ pre y, step (g pre) y = g (pre ++ [y])) (items : List α) : fold init items step = g items :=
  fold_prefix (fun pre s => s = g pre) items (fun pre y _ _ _ hs => hs ▸ hstep pre y) init h0

/-- A loop whose every iteration only updates the state and continues is a fold. -/
theorem forIn_fold {α σ R : Type} (g : α → σ → σ) (exit : σ → R) :
    ∀ (items : List α) (s : σ), forIn items (fun y next _ s => next (g y s)) exit s = exit (items.foldl (fun s y => g y s) s)
  | [], _ => rfl
  | y :: ys, s => forIn_fold g exit ys (g y s)

/-- A loop whose iterations all continue, each updating the state by `g`, is a fold. Show `h` by
splitting the iteration's cases (`intro y next exit s; split <;> rfl`). -/
theorem forIn_continue {α σ R : Type} {step : α → (σ → R) → (σ → R) → σ → R} {exit : σ → R} (g : α → σ → σ)
    (h : ∀ y next ex s, step y next ex s = next (g y s)) :
    ∀ (items : List α) (s : σ), forIn items step exit s = exit (items.foldl (fun s y => g y s) s)
  | [], _ => rfl
  | y :: ys, s => by rw [forIn_cons, h]; exact forIn_continue g h ys (g y s)

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

/-! ## `while` loops

Readable definitions run a `while` loop through `Ariadne.whileDo cond step exit s`, and its safety
condition is `Ariadne.whileSafe cond step exit s`: the loop ends within `loopBound` iterations, each of
them safe. Both unfold to `whileIn`. -/

theorem whileIn_zero {σ R : Type} (cond : σ → Bool) (step : (σ → R) → (σ → R) → σ → R) (exit stuck : σ → R)
    (s : σ) : whileIn 0 cond step exit stuck s = stuck s := rfl

theorem whileIn_succ {σ R : Type} (n : Nat) (cond : σ → Bool) (step : (σ → R) → (σ → R) → σ → R)
    (exit stuck : σ → R) (s : σ) :
    whileIn (n + 1) cond step exit stuck s = if cond s then step (whileIn n cond step exit stuck) exit s else exit s :=
  rfl

/-- An invariant of a `while` loop: if every iteration from a state satisfying `P` (where the condition
holds) ends in `Q` provided continuing and leaving do, and leaving (or running out of iterations) from `P`
ends in `Q`, then the loop does. -/
theorem whileIn_inv {σ R : Type} (P : σ → Prop) (Q : R → Prop) {cond : σ → Bool}
    {step : (σ → R) → (σ → R) → σ → R} {exit stuck : σ → R}
    (hstep : ∀ next ex s, P s → cond s = true → (∀ s', P s' → Q (next s')) → (∀ s', P s' → Q (ex s')) →
      Q (step next ex s))
    (hexit : ∀ s, P s → Q (exit s)) (hstuck : ∀ s, P s → Q (stuck s)) : ∀ (n : Nat) s, P s → Q (whileIn n cond step exit stuck s)
  | 0, s, h => hstuck s h
  | n + 1, s, h => by
    rw [whileIn_succ]
    split
    · exact hstep _ exit s h (by assumption) (fun s' h' => whileIn_inv P Q hstep hexit hstuck n s' h') hexit
    · exact hexit s h

/-- An invariant of a readable `while` loop (see `whileIn_inv`). -/
theorem whileDo_inv {σ R : Type} (P : σ → Prop) (Q : R → Prop) {cond : σ → Bool}
    {step : (σ → R) → (σ → R) → σ → R} {exit : σ → R}
    (hstep : ∀ next ex s, P s → cond s = true → (∀ s', P s' → Q (next s')) → (∀ s', P s' → Q (ex s')) →
      Q (step next ex s))
    (hexit : ∀ s, P s → Q (exit s)) (s : σ) (h : P s) : Q (whileDo cond step exit s) := by
  rw [whileDo_def]; exact whileIn_inv P Q hstep hexit hexit _ s h

/-- A `while` loop's safety condition, from a measure: an invariant `P` whose iterations are safe and
continue only to states of smaller measure, from a state whose measure is below `n`. -/
theorem whileIn_true {σ : Type} (P : σ → Prop) (μ : σ → Nat) {cond : σ → Bool}
    {step : (σ → Bool) → (σ → Bool) → σ → Bool} {exit : σ → Bool}
    (hstep : ∀ next ex s, P s → cond s = true → (∀ s', P s' → μ s' < μ s → next s' = true) →
      (∀ s', P s' → ex s' = true) → step next ex s = true)
    (hexit : ∀ s, P s → exit s = true) : ∀ (n : Nat) s, P s → μ s < n → whileIn n cond step exit (fun _ => false) s = true
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, s, h, hn => by
    rw [whileIn_succ]
    split
    · exact hstep _ exit s h (by assumption)
        (fun s' h' hm => whileIn_true P μ hstep hexit n s' h' (by omega)) hexit
    · exact hexit s h

/-- A readable `while` loop's safety condition, from a measure below `loopBound` (see `whileIn_true`). -/
theorem whileSafe_of_measure {σ : Type} (P : σ → Prop) (μ : σ → Nat) {cond : σ → Bool}
    {step : (σ → Bool) → (σ → Bool) → σ → Bool} {exit : σ → Bool}
    (hstep : ∀ next ex s, P s → cond s = true → (∀ s', P s' → μ s' < μ s → next s' = true) →
      (∀ s', P s' → ex s' = true) → step next ex s = true)
    (hexit : ∀ s, P s → exit s = true) (s : σ) (h : P s) (hμ : μ s < loopBound) : whileSafe cond step exit s = true := by
  rw [whileSafe_def]; exact whileIn_true P μ hstep hexit _ s h hμ

end Ariadne

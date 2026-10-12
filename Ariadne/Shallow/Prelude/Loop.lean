namespace Ariadne.Shallow

inductive Step (σ τ : Type) where
  | next (state : σ)
  | stop (state : σ)
  | ret (value : τ)
  deriving Repr, DecidableEq

inductive Exit (σ τ : Type) where
  | done (state : σ)
  | ret (value : τ)
  deriving Repr, DecidableEq

def Exit.finish (e : Exit σ τ) (rest : σ → τ) : τ :=
  match e with
  | .done s => rest s
  | .ret v => v

def Loop.each (xs : List α) (init : σ) (body : α → σ → Step σ τ) : Exit σ τ :=
  match xs with
  | [] => .done init
  | x :: xs => match body x init with
    | .next s => each xs s body
    | .stop s => .done s
    | .ret v => .ret v

def Loop.range (start count : Nat) (init : σ) (body : Nat → σ → Step σ τ) : Exit σ τ :=
  each (List.range' start count) init body

@[simp] theorem Loop.each_nil (init : σ) (body : α → σ → Step σ τ) :
    each [] init body = .done init := rfl

@[simp] theorem Loop.each_cons (x : α) (xs : List α) (init : σ) (body : α → σ → Step σ τ) :
    each (x :: xs) init body = match body x init with
      | .next s => each xs s body
      | .stop s => .done s
      | .ret v => .ret v := rfl

theorem Loop.each_invariant {xs : List α} {init : σ} {body : α → σ → Step σ τ}
    (I : σ → Prop) (Q : τ → Prop) (start : I init)
    (step : ∀ x ∈ xs, ∀ s, I s → match body x s with
      | .next s | .stop s => I s
      | .ret v => Q v) :
    match each xs init body with
    | .done s => I s
    | .ret v => Q v := by
  induction xs generalizing init with
  | nil => exact start
  | cons x xs ih =>
    have hx := step x (by simp) init start
    simp only [each]
    cases h : body x init with
    | next s =>
      simp only [h] at hx ⊢
      exact ih hx (fun y hy s hs => step y (by simp [hy]) s hs)
    | stop s => simpa only [h] using hx
    | ret v => simpa only [h] using hx

theorem Loop.each_foldl (xs : List α) (init : σ) (body : α → σ → σ) :
    each (τ := τ) xs init (fun x s => .next (body x s)) =
      .done (xs.foldl (fun s x => body x s) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => exact ih (body x init)

end Ariadne.Shallow

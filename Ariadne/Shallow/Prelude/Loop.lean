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

def Exit.elim (e : Exit σ τ) (done : σ → α) (ret : τ → α) : α :=
  match e with
  | .done s => done s
  | .ret v => ret v

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

/-- Exact half-open integer bounds; an inverted interval is empty. -/
def Loop.integers (start stop : Int) : List Int :=
  (List.range (stop - start).toNat).map (fun (i : Nat) => start + (i : Int))

@[simp] theorem Loop.integers_length (start stop : Int) :
    (integers start stop).length = (stop - start).toNat := by
  simp [integers]

@[simp] theorem Loop.mem_integers (x start stop : Int) :
    x ∈ integers start stop ↔ start ≤ x ∧ x < stop := by
  simp only [integers, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨lower, upper⟩
    refine ⟨(x - start).toNat, ?_, ?_⟩ <;> omega

theorem Loop.each_congr (xs : List α) (init : σ) (f g : α → σ → Step σ τ)
    (h : ∀ x ∈ xs, ∀ s, f x s = g x s) : each xs init f = each xs init g := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [each, h x (by simp)]
    cases g x init with
    | next s => exact ih s (fun y hy => h y (by simp [hy]))
    | stop s => rfl
    | ret v => rfl

theorem Loop.each_map (xs : List α) (f : α → β) (init : σ) (body : β → σ → Step σ τ) :
    each (xs.map f) init body = each xs init (fun x => body (f x)) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, each]
    cases body (f x) init with
    | next s => exact ih s
    | stop s => rfl
    | ret v => rfl

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

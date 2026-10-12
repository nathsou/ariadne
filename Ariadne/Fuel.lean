import Ariadne.Semantics

namespace Ariadne

/-- Flat approximation order: only timeout may acquire more information. In
particular, a completed runtime fault is just as stable as a successful result. -/
def Result.Refines (a b : Result α) : Prop :=
  a = .error .timeout ∨ a = b

namespace Result.Refines

theorem refl (a : Result α) : a.Refines a := Or.inr rfl

theorem trans {a b c : Result α} (ab : a.Refines b) (bc : b.Refines c) : a.Refines c := by
  rcases ab with h | h
  · exact Or.inl h
  · subst a; exact bc

theorem bind {a b : Result α} {f g : α → Result β}
    (ab : a.Refines b) (fg : ∀ x, (f x).Refines (g x)) :
    (a >>= f).Refines (b >>= g) := by
  rcases ab with h | h
  · subst a; exact Or.inl rfl
  · subst a
    cases b with
    | error e => exact refl _
    | ok x => exact fg x

theorem map {a b : Result α} (f : α → β) (ab : a.Refines b) :
    Result.Refines (a.map f) (b.map f) := by
  rcases ab with h | h
  · subst a; exact Or.inl rfl
  · subst a; exact refl _

theorem eq_of_completed {a b : Result α} (h : a.Refines b)
    (completed : a ≠ .error .timeout) : a = b := by
  exact h.resolve_left completed

end Result.Refines


-- Each evaluator clause is built from fuel-independent primitives, monadic
-- composition, and recursive calls at the smaller budget. Split only after
-- applying the bind/map rules, so effectful continuations use the same state.
set_option hygiene false in
local macro "refine_fuel" : tactic => `(tactic|
  repeat' first
  | exact Result.Refines.refl _
  | exact he _ _
  | exact ha _ _
  | exact hf _ _ _
  | exact hc _ _ _ _ _
  | exact ht _ _ _ _ _
  | exact hr _ _ _ _ _
  | exact hm _ _ _
  | exact hw _ _ _
  | exact hs _ _
  | exact hb _ _
  | exact hl _ _ _ _
  | apply Result.Refines.bind
  | apply Result.Refines.map
  | intro x
  | split)

private structure FuelStep (p : Program) (n : Nat) : Prop where
  expr : ∀ s e, (evalExpr p n s e).Refines (evalExpr p (n + 1) s e)
  args : ∀ s es, (evalArgs p n s es).Refines (evalArgs p (n + 1) s es)
  call : ∀ s f as, (apply p n s f as).Refines (apply p (n + 1) s f as)
  frame : ∀ s env ps b as, (callBody p n s env ps b as).Refines (callBody p (n + 1) s env ps b as)
  traverse : ∀ s cb xs i m, (traverse p n s cb xs i m).Refines (traverse p (n + 1) s cb xs i m)
  reduce : ∀ s cb xs a i, (reduce p n s cb xs a i).Refines (reduce p (n + 1) s cb xs a i)
  mapTraverse : ∀ s cb xs, (mapTraverse p n s cb xs).Refines (mapTraverse p (n + 1) s cb xs)
  assign : ∀ s t r, (assignTarget p n s t r).Refines (assignTarget p (n + 1) s t r)
  statement : ∀ s b, (exec p n s b).Refines (exec p (n + 1) s b)
  block : ∀ s bs, (execBlock p n s bs).Refines (execBlock p (n + 1) s bs)
  loop : ∀ s c b u, (loop p n s c b u).Refines (loop p (n + 1) s c b u)

private theorem fuel_step (p : Program) (n : Nat) : FuelStep p n := by
  induction n with
  | zero =>
    constructor
    all_goals intros; exact Or.inl rfl
  | succ n ih =>
    rcases ih with ⟨he, ha, hf, hc, ht, hr, hm, hw, hs, hb, hl⟩
    constructor
    · intro s e; cases e
      all_goals simp only [evalExpr]; refine_fuel
    · intro s es; cases es
      all_goals simp only [evalArgs]; refine_fuel
    · intros
      conv => lhs; unfold apply
      conv => rhs; unfold apply
      refine_fuel
    · intros
      conv => lhs; unfold callBody
      conv => rhs; unfold callBody
      refine_fuel
    · intros
      conv => lhs; unfold traverse
      conv => rhs; unfold traverse
      refine_fuel
    · intros
      conv => lhs; unfold reduce
      conv => rhs; unfold reduce
      refine_fuel
    · intros
      conv => lhs; unfold mapTraverse
      conv => rhs; unfold mapTraverse
      refine_fuel
    · intros
      conv => lhs; unfold assignTarget
      conv => rhs; unfold assignTarget
      refine_fuel
    · intro s b; cases b
      all_goals simp only [exec]; refine_fuel
    · intro s bs; cases bs
      all_goals simp only [execBlock]; refine_fuel
    · intros
      conv => lhs; unfold loop
      conv => rhs; unfold loop
      refine_fuel

/-- Lift the one-step proof to arbitrary larger budgets. -/
theorem Result.refines_of_step (f : Nat → Result α)
    (step : ∀ n, (f n).Refines (f (n + 1))) {small large : Nat}
    (le : small ≤ large) : (f small).Refines (f large) := by
  induction le with
  | refl => exact Refines.refl _
  | step le ih => exact ih.trans (step _)

theorem evalExpr_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (e : Expr) :
    (evalExpr p small s e).Refines (evalExpr p large s e) :=
  Result.refines_of_step (fun n => evalExpr p n s e)
    (fun n => (fuel_step p n).expr s e) le

theorem evalArgs_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (es : List Expr) :
    (evalArgs p small s es).Refines (evalArgs p large s es) :=
  Result.refines_of_step (fun n => evalArgs p n s es)
    (fun n => (fuel_step p n).args s es) le

theorem apply_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (fn : Value) (args : List Value) :
    (apply p small s fn args).Refines (apply p large s fn args) :=
  Result.refines_of_step (fun n => apply p n s fn args)
    (fun n => (fuel_step p n).call s fn args) le

theorem callBody_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (env : Env) (ps : List Param) (body : Stmt) (args : List Value) :
    (callBody p small s env ps body args).Refines (callBody p large s env ps body args) :=
  Result.refines_of_step (fun n => callBody p n s env ps body args)
    (fun n => (fuel_step p n).frame s env ps body args) le

theorem traverse_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (cb : Value) (xs : List Value) (i : Nat) (mode : String) :
    (traverse p small s cb xs i mode).Refines (traverse p large s cb xs i mode) :=
  Result.refines_of_step (fun n => traverse p n s cb xs i mode)
    (fun n => (fuel_step p n).traverse s cb xs i mode) le

theorem reduce_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (cb : Value) (xs : List Value) (acc : Value) (i : Nat) :
    (reduce p small s cb xs acc i).Refines (reduce p large s cb xs acc i) :=
  Result.refines_of_step (fun n => reduce p n s cb xs acc i)
    (fun n => (fuel_step p n).reduce s cb xs acc i) le

theorem mapTraverse_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (cb : Value) (xs : List (Value × Value)) :
    (mapTraverse p small s cb xs).Refines (mapTraverse p large s cb xs) :=
  Result.refines_of_step (fun n => mapTraverse p n s cb xs)
    (fun n => (fuel_step p n).mapTraverse s cb xs) le

theorem assignTarget_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (target rhs : Expr) :
    (assignTarget p small s target rhs).Refines (assignTarget p large s target rhs) :=
  Result.refines_of_step (fun n => assignTarget p n s target rhs)
    (fun n => (fuel_step p n).assign s target rhs) le

theorem exec_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (body : Stmt) :
    (exec p small s body).Refines (exec p large s body) :=
  Result.refines_of_step (fun n => exec p n s body)
    (fun n => (fuel_step p n).statement s body) le

theorem execBlock_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (body : List Stmt) :
    (execBlock p small s body).Refines (execBlock p large s body) :=
  Result.refines_of_step (fun n => execBlock p n s body)
    (fun n => (fuel_step p n).block s body) le

theorem loop_fuel_mono (p : Program) {small large : Nat} (le : small ≤ large)
    (s : State) (guard : Expr) (body : Stmt) (update : Option Stmt) :
    (loop p small s guard body update).Refines (loop p large s guard body update) :=
  Result.refines_of_step (fun n => loop p n s guard body update)
    (fun n => (fuel_step p n).loop s guard body update) le

theorem runState_fuel_mono (p : Program) (name : String) (args : List Value)
    {small large : Nat} (le : small ≤ large) :
    (runState p name small args).Refines (runState p name large args) :=
  apply_fuel_mono p le {} (.function name) args

theorem run_fuel_mono (p : Program) (name : String) (args : List Value)
    {small large : Nat} (le : small ≤ large) :
    (run p name small args).Refines (run p name large args) :=
  (runState_fuel_mono p name args le).map Prod.fst

/-- Budget-independent convergence, defined from finite approximations. This is
not a separate ECMAScript semantics or an independent operational rule system. -/
def Converges (evaluate : Nat → Result α) (outcome : Result α) : Prop :=
  outcome ≠ .error .timeout ∧ ∃ fuel, evaluate fuel = outcome

/-- For a monotone evaluator, convergence means the same result at every
sufficiently large budget, including the same final heap on successful runs. -/
theorem converges_iff_eventually (evaluate : Nat → Result α)
    (mono : ∀ {n m}, n ≤ m → (evaluate n).Refines (evaluate m)) (outcome : Result α) :
    Converges evaluate outcome ↔
      outcome ≠ .error .timeout ∧ ∃ threshold, ∀ fuel, threshold ≤ fuel → evaluate fuel = outcome := by
  constructor
  · rintro ⟨completed, threshold, h⟩
    refine ⟨completed, threshold, ?_⟩
    intro fuel le
    have eq := (mono le).eq_of_completed (by simpa [h] using completed)
    exact eq.symm.trans h
  · rintro ⟨completed, threshold, h⟩
    exact ⟨completed, threshold, h threshold (Nat.le_refl _)⟩

theorem converges_deterministic (evaluate : Nat → Result α)
    (mono : ∀ {n m}, n ≤ m → (evaluate n).Refines (evaluate m))
    {a b : Result α} (ha : Converges evaluate a) (hb : Converges evaluate b) : a = b := by
  rcases (converges_iff_eventually evaluate mono a).mp ha with ⟨_, n, hn⟩
  rcases (converges_iff_eventually evaluate mono b).mp hb with ⟨_, m, hm⟩
  exact (hn (max n m) (Nat.le_max_left ..)).symm.trans
    (hm (max n m) (Nat.le_max_right ..))

def Executes (p : Program) (name : String) (args : List Value)
    (outcome : Result (Value × State)) : Prop :=
  Converges (fun fuel => runState p name fuel args) outcome

theorem executes_deterministic {p : Program} {name : String} {args : List Value}
    {a b : Result (Value × State)} (ha : Executes p name args a) (hb : Executes p name args b) :
    a = b :=
  converges_deterministic _ (runState_fuel_mono p name args) ha hb

theorem returns_deterministic {p : Program} {name : String} {args : List Value}
    {a b : Value} (ha : Returns p name args a) (hb : Returns p name args b) : a = b := by
  have h := converges_deterministic _ (run_fuel_mono p name args)
    (a := .ok a) (b := .ok b) ⟨(by intro h; cases h), ha⟩ ⟨(by intro h; cases h), hb⟩
  exact Except.ok.inj h

end Ariadne

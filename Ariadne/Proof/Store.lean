import Ariadne.Model.Store

/-!
# The value model agrees with the store model

For a program that passes the static check, running a method in the value model
(`runMethod`: the object is the binding `this`, copied into callees and back) gives
exactly the result of the store model (`runMethodStore`: one object changed in
place). The proof is by induction on the fuel: the value model runs in the
environment `fill σ env` where the store model runs in `env` with store `σ`.

The store model evaluates expressions without threading the store. That is exact
because a method an expression may call changes no state: `scoped_pure_keeps`
proves that such a call, run in the store model, returns the store it was given.
-/

set_option linter.unusedSimpArgs false

namespace Ariadne

theorem stmtsThisFree_append : ∀ (a b : List Stmt), stmtsThisFree a = true → stmtsThisFree b = true →
    stmtsThisFree (a ++ b) = true
  | [], _, _, hb => hb
  | s :: a, b, ha, hb => by
    simp only [stmtsThisFree, Bool.and_eq_true, List.cons_append] at ha ⊢
    exact ⟨ha.1, stmtsThisFree_append a b ha.2 hb⟩

theorem casesThisFree_drop : ∀ (cases : List (Option Expr × List Stmt)) (i : Nat), casesThisFree cases = true →
    stmtsThisFree ((cases.drop i).flatMap (·.2)) = true
  | [], _, _ => by simp [stmtsThisFree]
  | (_, body) :: rest, 0, h => by
    simp only [casesThisFree, Bool.and_eq_true] at h
    simp only [List.drop_zero, List.flatMap_cons]
    exact stmtsThisFree_append _ _ h.1 (by simpa using casesThisFree_drop rest 0 h.2)
  | (_, _) :: rest, i + 1, h => by
    simp only [casesThisFree, Bool.and_eq_true] at h
    simpa using casesThisFree_drop rest i h.2

/-- At most one `this` among the keys. -/
def uniq : List String → Bool
  | [] => true
  | x :: xs => if x = "this" then !xs.contains "this" else uniq xs

/-- At most one binding of `this`. -/
def Unique (env : Env) : Prop := uniq (env.map Prod.fst) = true

def Outcome.env : Outcome → Env
  | .normal env | .returned _ env | .broke env | .continued env => env

/-! ## Environments where `this` is the store -/

theorem fill_cons (σ : JSValue) (x : String) (v : JSValue) (env : Env) (hx : x ≠ "this") :
    fill σ ((x, v) :: env) = (x, v) :: fill σ env := by
  simp [fill, hx]

theorem fill_cons_this (σ w : JSValue) (env : Env) : fill σ (("this", w) :: env) = ("this", σ) :: fill σ env := by
  simp [fill]

theorem fill_append (σ : JSValue) (bs env : Env) (h : bs.all (·.1 != "this") = true) :
    fill σ (bs ++ env) = bs ++ fill σ env := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨x, v⟩ := b
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    rw [fill_cons σ x v _ h.1, ih h.2]

theorem fill_length (σ : JSValue) (env : Env) : (fill σ env).length = env.length := by simp [fill]

theorem lookup_fill (σ : JSValue) (x : String) : ∀ env : Env,
    (fill σ env).lookup x = if x = "this" then (env.lookup x).map fun _ => σ else env.lookup x
  | [] => by simp [fill, List.lookup]
  | (y, v) :: env => by
    have ih := lookup_fill σ x env
    simp only [fill] at ih
    simp only [fill, List.map_cons]
    by_cases hy : y = "this"
    · subst hy
      by_cases hx : x = "this"
      · subst hx; simp [List.lookup]
      · simp [List.lookup, beq_eq_false_iff_ne.mpr hx, ih, hx]
    · by_cases hx : x = y
      · subst hx; simp [List.lookup, hy]
      · simp [List.lookup, hy, beq_eq_false_iff_ne.mpr hx, ih]

theorem lookup_fill_ne (σ : JSValue) (x : String) (env : Env) (hx : x ≠ "this") :
    (fill σ env).lookup x = env.lookup x := by
  rw [lookup_fill]; simp [hx]

theorem assign_fill (σ : JSValue) (x : String) (v : JSValue) (hx : x ≠ "this") : ∀ env : Env,
    assign x v (fill σ env) = (assign x v env).map (fill σ)
  | [] => by simp [fill, assign, Except.map]
  | (y, w) :: env => by
    have ih := assign_fill σ x v hx env
    simp only [fill] at ih
    simp only [fill, List.map_cons]
    by_cases hy : y = x
    · subst hy; simp [assign, hx, Except.map, fill]
    · have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      by_cases hyt : y = "this"
      · simp only [hyt, ite_true, assign] at ih ⊢
        rw [show ("this" == x) = false from by subst hyt; exact hyx]
        simp only [Bool.false_eq_true, ite_false, ih]
        cases assign x v env <;> simp [Except.map, bind, Except.bind, pure, Except.pure, fill]
      · simp only [hyt, ite_false, assign, hyx, Bool.false_eq_true, ih]
        cases assign x v env <;> simp [Except.map, bind, Except.bind, pure, Except.pure, hyt, fill]

theorem restore_fill (σ σ' : JSValue) (outer inner : Env) :
    Ariadne.restore (fill σ outer) (fill σ' inner) = fill σ' (Ariadne.restore outer inner) := by
  simp [Ariadne.restore, fill, fill_length, List.map_drop]

theorem Outcome.restore_fill (σ σ' : JSValue) (outer : Env) (o : Outcome) :
    (o.fill σ').restore (Ariadne.fill σ outer) = (o.restore outer).fill σ' := by
  cases o <;> simp [Outcome.fill, Outcome.restore, Ariadne.restore_fill]

theorem thisOf_fill (σ : JSValue) (env : Env) : thisOf (Ariadne.fill σ env) = storeOf σ env := by
  unfold thisOf storeOf
  rw [lookup_fill]
  cases env.lookup "this" <;> simp

theorem fill_free (σ : JSValue) : ∀ env : Env, env.all (·.1 != "this") = true → fill σ env = env
  | [], _ => rfl
  | (x, v) :: env, h => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [fill_cons σ x v env h.1, fill_free σ env h.2]

theorem bindParams_keys : ∀ (xs : List String) (vs : List JSValue), (bindParams xs vs).map Prod.fst = xs
  | [], _ => rfl
  | _ :: xs, [] => by simp [bindParams, bindParams_keys xs []]
  | _ :: xs, _ :: vs => by simp [bindParams, bindParams_keys xs vs]

theorem bindParams_free (xs : List String) (vs : List JSValue) (h : "this" ∉ xs) :
    (bindParams xs vs).all (·.1 != "this") = true := by
  rw [List.all_eq_true]
  intro b hb
  have : b.1 ∈ (bindParams xs vs).map Prod.fst := List.mem_map_of_mem hb
  rw [bindParams_keys] at this
  simp only [bne_iff_ne, ne_eq]
  exact fun h' => h (h' ▸ this)

/-! ## At most one `this` -/

theorem assign_keys (x : String) (v : JSValue) : ∀ (env env' : Env), assign x v env = .ok env' →
    env'.map Prod.fst = env.map Prod.fst
  | [], _, h => by simp [assign] at h
  | (y, w) :: env, env', h => by
    by_cases hy : y = x
    · subst hy; simp [assign] at h; subst h; rfl
    · simp only [assign, beq_eq_false_iff_ne.mpr hy, Bool.false_eq_true, ite_false] at h
      cases ha : assign x v env with
      | error e => simp [ha, bind, Except.bind] at h
      | ok env'' =>
        simp [ha, bind, Except.bind, pure, Except.pure] at h; subst h
        simp [assign_keys x v env env'' ha]

theorem uniq_of_free : ∀ xs : List String, xs.contains "this" = false → uniq xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp [uniq, Ne.symm h.1, uniq_of_free xs (by simpa using h.2)]

theorem uniq_drop : ∀ (k : Nat) (xs : List String), uniq xs = true → uniq (xs.drop k) = true
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | k + 1, x :: xs, h => by
    simp only [List.drop_succ_cons]
    apply uniq_drop k xs
    unfold uniq at h
    split at h
    · exact uniq_of_free xs (by simpa using h)
    · exact h

theorem unique_cons (x : String) (v : JSValue) (env : Env) (hx : x ≠ "this") (h : Unique env) :
    Unique ((x, v) :: env) := by
  unfold Unique at *; simp [uniq, hx, h]

theorem unique_append (bs env : Env) (hb : bs.all (·.1 != "this") = true) (h : Unique env) :
    Unique (bs ++ env) := by
  induction bs with
  | nil => exact h
  | cons b bs ih =>
    obtain ⟨x, v⟩ := b
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    exact unique_cons x v _ hb.1 (ih hb.2)

theorem unique_restore (outer env : Env) (h : Unique env) : Unique (Ariadne.restore outer env) := by
  unfold Unique Ariadne.restore at *
  rw [List.map_drop]; exact uniq_drop _ _ h

theorem unique_assign (x : String) (v : JSValue) (env env' : Env) (ha : assign x v env = .ok env') (h : Unique env) :
    Unique env' := by
  unfold Unique at *; rw [assign_keys x v env env' ha]; exact h

theorem unique_fill (σ : JSValue) (env : Env) (h : Unique env) : Unique (fill σ env) := by
  unfold Unique fill at *
  have : (env.map fun (x, v) => if x = "this" then (x, σ) else (x, v)).map Prod.fst = env.map Prod.fst := by
    simp only [List.map_map]; congr 1; funext ⟨x, v⟩; by_cases hx : x = "this" <;> simp [hx]
  rw [this]; exact h

/-- Assigning `this` (the only binding of it) in the filled environment refills it. -/
theorem assign_fill_this (σ t : JSValue) : ∀ env : Env, Unique env → (env.lookup "this").isSome = true →
    assign "this" t (fill σ env) = .ok (fill t env)
  | [], _, h => by simp [List.lookup] at h
  | (y, w) :: env, hu, h => by
    by_cases hy : y = "this"
    · subst hy
      unfold Unique at hu
      simp only [List.map_cons, uniq, ite_true, Bool.not_eq_true'] at hu
      have hf : env.all (·.1 != "this") = true := by
        rw [List.all_eq_true]; intro b hb
        have hm : b.1 ∈ env.map Prod.fst := List.mem_map_of_mem hb
        simp only [bne_iff_ne, ne_eq]; intro he
        rw [he] at hm
        simp [List.contains_iff_mem, hm] at hu
      rw [fill_cons_this, fill_cons_this, fill_free σ env hf, fill_free t env hf]
      simp [assign]
    · have hu' : Unique env := by unfold Unique at *; simpa [uniq, hy] using hu
      have h' : (env.lookup "this").isSome = true := by
        simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hy)] using h
      have ih := assign_fill_this σ t env hu' h'
      rw [fill_cons σ y w env hy, fill_cons t y w env hy]
      simp [assign, beq_eq_false_iff_ne.mpr hy, ih, bind, Except.bind, pure, Except.pure]

theorem setStateMap_fill (σ : JSValue) (env : Env) (f : String) (kvs : List (JSString × JSValue)) (hu : Unique env) :
    setStateMap (fill σ env) f kvs = (storeSet σ env f kvs).map (fun σ' => fill σ' env) := by
  unfold setStateMap storeSet
  rw [lookup_fill]
  cases hl : env.lookup "this" with
  | none => cases σ <;> simp [Except.map]
  | some w =>
    cases σ <;> simp [Except.map]
    exact assign_fill_this _ _ env hu (by simp [hl])

/-! ## The models agree -/

/-- The program's methods take `this` first (and only once) and never bind or assign it. -/
def Program.storeOk (p : Program) : Prop :=
  ∀ fn ∈ p, fn.method = true → (∃ rest, fn.params = "this" :: rest ∧ "this" ∉ rest) ∧ stmtsThisFree fn.body = true

/-- A store-model outcome, seen in the value model: `this` is the final store. -/
def RMap (r : Outcome × JSValue) : Outcome := r.1.fill r.2

theorem Outcome.fill_env (σ : JSValue) (o : Outcome) : (o.fill σ).env = Ariadne.fill σ o.env := by cases o <;> rfl

theorem storeOf_ok {σ t : JSValue} {env : Env} (h : storeOf σ env = .ok t) : t = σ ∧ (env.lookup "this").isSome := by
  unfold storeOf at h; split at h <;> simp_all

theorem free_singleton (x : String) (v : JSValue) (hx : x ≠ "this") : [(x, v)].all (·.1 != "this") = true := by
  simp [hx]

/-- The same first step, then continuations related by `F`. -/
theorem bind_map {ε α β γ : Type} (x : Except ε α) {f : α → Except ε β} {g : α → Except ε γ} {F : γ → β}
    (h : ∀ a, x = .ok a → f a = (g a).map F) : (x >>= f) = (x >>= g).map F := by
  cases x with
  | error e => rfl
  | ok a => exact h a rfl

theorem bind_ok {ε α γ : Type} (x : Except ε α) {g : α → Except ε γ} {P : γ → Prop}
    (h : ∀ a, x = .ok a → ∀ r, g a = .ok r → P r) : ∀ r, (x >>= g) = .ok r → P r := by
  cases x with
  | error e => intro r h'; cases h'
  | ok a => exact h a rfl

/-- Both sides fault alike. -/
macro "errs" : tactic => `(tactic|
  ((try clear ihS ihs ihL ihC hp) <;> constructor <;> (try intro r h) <;>
    simp_all [bind, Except.bind, Except.map, pure, Except.pure]))

macro "errs'" hyp:ident : tactic => `(tactic|
  ((try clear ihS ihs ihL ihC hp) <;> constructor <;> (try intro r h) <;>
    simp [$hyp:ident, bind, Except.bind, Except.map, pure, Except.pure] at *))

/-- Agreement at fuel `n`: for statement lists, one statement, loops and method calls
(the four parts of `agree`, proved one fuel step at a time so that the step's cases
are separate lemmas, checked in parallel). -/
def AgS (p : Program) (n : Nat) : Prop :=
  ∀ σ env ss, stmtsThisFree ss = true → Unique env →
    execStmts p n (fill σ env) ss = (sExecStmts p n σ env ss).map RMap ∧
    ∀ r, sExecStmts p n σ env ss = .ok r → Unique r.1.env

def AgOne (p : Program) (n : Nat) (s : Stmt) : Prop :=
  ∀ σ env, stmtThisFree s = true → Unique env →
    execStmt p n (fill σ env) s = (sExecStmt p n σ env s).map RMap ∧
    ∀ r, sExecStmt p n σ env s = .ok r → Unique r.1.env

def AgL (p : Program) (n : Nat) : Prop :=
  ∀ σ env bss body, stmtsThisFree body = true → (∀ bs ∈ bss, bs.all (·.1 != "this") = true) → Unique env →
    loop p n (fill σ env) bss body = (sLoop p n σ env bss body).map RMap ∧
    ∀ r, sLoop p n σ env bss body = .ok r → Unique r.1.env

def AgC (p : Program) (n : Nat) : Prop := ∀ m σ vs, callState p n m (σ :: vs) = sCallState p n m σ vs

def Ag (p : Program) (n : Nat) : Prop :=
  AgS p n ∧
    (∀ σ env s, stmtThisFree s = true → Unique env →
      execStmt p n (fill σ env) s = (sExecStmt p n σ env s).map RMap ∧
      ∀ r, sExecStmt p n σ env s = .ok r → Unique r.1.env) ∧
    AgL p n ∧ AgC p n

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_stmts {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) :
    AgS p (n + 1) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgL AgC at *
  intro σ env ss hf hu
  cases ss with
  | nil =>
    refine ⟨by simp [execStmts, sExecStmts, Except.map, RMap, Outcome.fill], ?_⟩
    intro r h; simp [sExecStmts] at h; subst h; exact hu
  | cons s rest =>
    simp only [stmtsThisFree, Bool.and_eq_true] at hf
    obtain ⟨h1, h2⟩ := ihs σ env s hf.1 hu
    simp only [execStmts, sExecStmts]
    rw [h1]
    cases hs : sExecStmt p n σ env s with
    | error e => exact ⟨by simp [Except.map, bind, Except.bind], by simp [bind, Except.bind]⟩
    | ok r =>
      obtain ⟨o, σ'⟩ := r
      have hu' := h2 _ hs
      cases o with
      | normal e =>
        obtain ⟨h3, h4⟩ := ihS σ' e rest hf.2 hu'
        simp only [Except.map, bind, Except.bind, RMap, Outcome.fill]
        exact ⟨h3, h4⟩
      | returned v e =>
        simp only [Except.map, bind, Except.bind, RMap, Outcome.fill]
        exact ⟨trivial, fun r h => by cases h; exact hu'⟩
      | broke e =>
        simp only [Except.map, bind, Except.bind, RMap, Outcome.fill]
        exact ⟨trivial, fun r h => by cases h; exact hu'⟩
      | continued e =>
        simp only [Except.map, bind, Except.bind, RMap, Outcome.fill]
        exact ⟨trivial, fun r h => by cases h; exact hu'⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_const {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (x : String) (e : Expr) :
    AgOne p (n + 1) (.const x e) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  have hx : x ≠ "this" := by simpa [stmtThisFree] using hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    refine ⟨by simp [bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.fill, fill_cons σ x v env hx], ?_⟩
    intro r h; simp [bind, Except.bind, pure, Except.pure] at h; subst h; exact unique_cons x v env hx hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_let {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (x : String) (e : Expr) :
    AgOne p (n + 1) (.let_ x e) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  have hx : x ≠ "this" := by simpa [stmtThisFree] using hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    refine ⟨by simp [bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.fill, fill_cons σ x v env hx], ?_⟩
    intro r h; simp [bind, Except.bind, pure, Except.pure] at h; subst h; exact unique_cons x v env hx hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_assign {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (x : String) (e : Expr) :
    AgOne p (n + 1) (.assign x e) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  have hx : x ≠ "this" := by simpa [stmtThisFree] using hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    rw [show (do let v ← Except.ok v; return Outcome.normal (← assign x v (fill σ env)) : Except Fault Outcome) =
        (do return Outcome.normal (← assign x v (fill σ env))) from rfl, assign_fill σ x v hx]
    cases ha : assign x v env with
    | error err => errs' ha
    | ok env' =>
      refine ⟨by simp [ha, bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.fill], ?_⟩
      intro r h; simp [ha, bind, Except.bind, pure, Except.pure] at h; subst h
      exact unique_assign x v env env' ha hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_ret {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (e : Expr) :
    AgOne p (n + 1) (.ret e) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    refine ⟨by simp [bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.fill], ?_⟩
    intro r h; simp [bind, Except.bind, pure, Except.pure] at h; subst h; exact hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_brk {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) :
    AgOne p (n + 1) (.brk) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  exact ⟨by simp [execStmt, sExecStmt, Except.map, RMap, Outcome.fill],
    fun r h => by simp [sExecStmt] at h; subst h; exact hu⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_cont {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) :
    AgOne p (n + 1) (.cont) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  exact ⟨by simp [execStmt, sExecStmt, Except.map, RMap, Outcome.fill],
    fun r h => by simp [sExecStmt] at h; subst h; exact hu⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_block {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (ss : List Stmt) :
    AgOne p (n + 1) (.block ss) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree] at hf
  simp only [execStmt, sExecStmt]
  obtain ⟨h1, h2⟩ := ihS σ env ss hf hu
  rw [h1]
  cases hs : sExecStmts p n σ env ss with
  | error err => errs
  | ok r =>
    obtain ⟨o, σ'⟩ := r
    refine ⟨by simp [bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.restore_fill], ?_⟩
    intro r h; simp [bind, Except.bind, pure, Except.pure] at h; subst h
    have := h2 _ hs
    cases o <;> simp [Outcome.restore, Outcome.env] at this ⊢ <;> first | exact this | exact unique_restore _ _ this

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_ite {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (c : Expr) (yes no : List Stmt) :
    AgOne p (n + 1) (.ite c yes no) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree, Bool.and_eq_true] at hf
  simp only [execStmt, sExecStmt]
  cases hc : evalExpr p n (fill σ env) c with
  | error err => errs
  | ok cv =>
    have branchCase : ∀ b, stmtsThisFree b = true →
        (do let o ← execStmts p n (fill σ env) b; pure (o.restore (fill σ env)) : Except Fault Outcome) =
          (do let (o, σ') ← sExecStmts p n σ env b; pure (o.restore env, σ')).map RMap ∧
        ∀ r, (do let (o, σ') ← sExecStmts p n σ env b; pure (o.restore env, σ') : Except Fault _) = .ok r →
          Unique r.1.env := by
      intro b hb
      obtain ⟨h1, h2⟩ := ihS σ env b hb hu
      rw [h1]
      cases hs : sExecStmts p n σ env b with
      | error err => errs
      | ok r =>
        obtain ⟨o, σ'⟩ := r
        refine ⟨by simp [bind, Except.bind, pure, Except.pure, Except.map, RMap, Outcome.restore_fill], ?_⟩
        intro r h; simp [bind, Except.bind, pure, Except.pure] at h; subst h
        have := h2 _ hs
        cases o <;> simp [Outcome.restore, Outcome.env] at this ⊢ <;>
          first | exact this | exact unique_restore _ _ this
    cases cv
    case bool b =>
      cases b
      · exact branchCase no hf.2
      · exact branchCase yes hf.1
    all_goals errs

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_switch {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (e : Expr) (cases : List (Option Expr × List Stmt)) :
    AgOne p (n + 1) (.switch e cases) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree] at hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    simp only [bind, Except.bind]
    cases hfc : findCase p n (fill σ env) v cases 0 with
    | error err => errs
    | ok oi =>
      cases oi with
      | none =>
        exact ⟨by simp [Except.map, RMap, Outcome.fill], fun r h => by simp at h; subst h; exact hu⟩
      | some i =>
        obtain ⟨h1, h2⟩ := ihS σ env _ (casesThisFree_drop cases i hf) hu
        simp only
        rw [h1]
        cases hs : sExecStmts p n σ env ((cases.drop i).flatMap (·.2)) with
        | error err => errs
        | ok r =>
          obtain ⟨o, σ'⟩ := r
          have hu' := h2 _ hs
          simp only [Except.map, RMap]
          rw [Outcome.restore_fill]
          cases ho : o.restore env with
          | broke e' =>
            have : Unique e' := by
              cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
            exact ⟨by simp [Outcome.fill], fun r h => by simp at h; subst h; exact this⟩
          | normal e' =>
            have : Unique e' := by
              cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
            exact ⟨by simp [Outcome.fill], fun r h => by simp at h; subst h; exact this⟩
          | continued e' =>
            have : Unique e' := by
              cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
            exact ⟨by simp [Outcome.fill], fun r h => by simp at h; subst h; exact this⟩
          | returned w e' =>
            have : Unique e' := by
              cases o <;> simp [Outcome.restore] at ho <;> (try subst ho) <;> simp_all [Outcome.env]
            exact ⟨by simp [Outcome.fill], fun r h => by simp at h; subst h; exact this⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_forOf {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (x : String) (e : Expr) (body : List Stmt) :
    AgOne p (n + 1) (.forOf x e body) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    simp only [bind, Except.bind]
    cases v
    case array xs =>
      exact ihL σ env _ body hf.2 (fun bs hb => by
        simp only [List.mem_map] at hb; obtain ⟨w, _, rfl⟩ := hb; exact free_singleton x w hf.1) hu
    all_goals errs

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_forEntries {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (i x : String) (e : Expr) (body : List Stmt) :
    AgOne p (n + 1) (.forEntries i x e body) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
  simp only [execStmt, sExecStmt]
  cases he : evalExpr p n (fill σ env) e with
  | error err => errs
  | ok v =>
    simp only [bind, Except.bind]
    cases v
    case array xs =>
      exact ihL σ env _ body hf.2 (fun bs hb => by
        simp only [entryBindings, List.mem_map] at hb; obtain ⟨w, _, rfl⟩ := hb
        simp [hf.1.1, hf.1.2]) hu
    all_goals errs

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_forRange {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (i k : String) (body : List Stmt) :
    AgOne p (n + 1) (.forRange i k body) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
  simp only [execStmt, sExecStmt]
  cases hl : (fill σ env).lookup k with
  | none => errs
  | some v =>
    cases v
    case number m =>
      exact ihL σ env _ body hf.2 (fun bs hb => by
        simp only [rangeBindings, List.mem_map] at hb; obtain ⟨w, _, rfl⟩ := hb
        exact free_singleton i _ hf.1) hu
    all_goals errs

set_option linter.unusedVariables false in
theorem agree_while {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (c : Expr) (body : List Stmt) :
    AgOne p (n + 1) (.while_ c body) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [stmtThisFree] at hf
  simp only [execStmt, sExecStmt]
  exact ihL σ env _ _ (by simp [stmtsThisFree, stmtThisFree, hf])
    (fun bs hb => by simp only [List.mem_replicate] at hb; rw [hb.2]; rfl) hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_stateSet {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (f : String) (k v : Expr) :
    AgOne p (n + 1) (.stateSet f k v) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [execStmt, sExecStmt]
  refine ⟨?_, ?_⟩
  · refine bind_map _ fun kvs _ => bind_map _ fun kv _ => bind_map _ fun key _ => bind_map _ fun w _ => ?_
    show (setStateMap (fill σ env) f (mapPut kvs key w) >>= fun e => pure (Outcome.normal e)) =
      (storeSet σ env f (mapPut kvs key w) >>= fun σ' => pure (Outcome.normal env, σ')).map RMap
    rw [setStateMap_fill σ env f _ hu]
    cases storeSet σ env f (mapPut kvs key w) <;> rfl
  · refine bind_ok _ fun kvs _ => bind_ok _ fun kv _ => bind_ok _ fun key _ => bind_ok _ fun w _ => ?_
    intro r h
    cases hs : storeSet σ env f (mapPut kvs key w) <;> simp [hs, bind, Except.bind, pure, Except.pure] at h
    subst h; exact hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_stateDelete {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (f : String) (k : Expr) :
    AgOne p (n + 1) (.stateDelete f k) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [execStmt, sExecStmt]
  refine ⟨?_, ?_⟩
  · refine bind_map _ fun kvs _ => bind_map _ fun kv _ => bind_map _ fun key _ => ?_
    show (setStateMap (fill σ env) f (mapDel kvs key) >>= fun e => pure (Outcome.normal e)) =
      (storeSet σ env f (mapDel kvs key) >>= fun σ' => pure (Outcome.normal env, σ')).map RMap
    rw [setStateMap_fill σ env f _ hu]
    cases storeSet σ env f (mapDel kvs key) <;> rfl
  · refine bind_ok _ fun kvs _ => bind_ok _ fun kv _ => bind_ok _ fun key _ => ?_
    intro r h
    cases hs : storeSet σ env f (mapDel kvs key) <;> simp [hs, bind, Except.bind, pure, Except.pure] at h
    subst h; exact hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_callThis {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) (m : String) (args : List Expr) :
    AgOne p (n + 1) (.callThis m args) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgOne AgL AgC at *
  intro σ env hf hu
  simp only [execStmt, sExecStmt, thisOf_fill, ihC]
  refine ⟨?_, ?_⟩
  · refine bind_map _ fun vs _ => bind_map _ fun t ht => bind_map _ fun r _ => ?_
    obtain ⟨rfl, hpres⟩ := storeOf_ok ht
    show (assign "this" r.2 (fill t env) >>= fun e => pure (Outcome.normal e)) = (pure (Outcome.normal env, r.2) : Except Fault _).map RMap
    rw [assign_fill_this t r.2 env hu hpres]; rfl
  · refine bind_ok _ fun vs _ => bind_ok _ fun t _ => bind_ok _ fun r _ => ?_
    intro r' h; simp [pure, Except.pure] at h; subst h; exact hu

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_loop {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) :
    AgL p (n + 1) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgL AgC at *
  intro σ env bss body hf hb hu
  cases bss with
  | nil =>
    refine ⟨by simp [loop, sLoop, Except.map, RMap, Outcome.fill], ?_⟩
    intro r h; simp [sLoop] at h; subst h; exact hu
  | cons bs rest =>
    have hbs := hb bs (by simp)
    have hrest : ∀ b ∈ rest, b.all (·.1 != "this") = true := fun b h => hb b (by simp [h])
    simp only [loop, sLoop]
    rw [← fill_append σ bs env hbs]
    obtain ⟨h1, h2⟩ := ihS σ (bs ++ env) body hf (unique_append bs env hbs hu)
    rw [h1]
    cases hs : sExecStmts p n σ (bs ++ env) body with
    | error e => exact ⟨by simp [Except.map, bind, Except.bind], by simp [bind, Except.bind]⟩
    | ok r =>
      obtain ⟨o, σ'⟩ := r
      have hu' := h2 _ hs
      simp only [Except.map, bind, Except.bind, RMap]
      rw [Outcome.restore_fill]
      cases ho : o.restore env with
      | returned v e =>
        have : Unique e := by
          have := congrArg Outcome.env ho; cases o <;> simp_all [Outcome.restore, Outcome.env]
        simp only [Outcome.fill]; exact ⟨trivial, fun r h => by cases h; exact this⟩
      | broke e =>
        have : Unique e := by
          cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
        simp only [Outcome.fill]; exact ⟨trivial, fun r h => by cases h; exact this⟩
      | normal e =>
        have : Unique e := by
          cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
        simp only [Outcome.fill]
        exact ihL σ' e rest body hf hrest this
      | continued e =>
        have : Unique e := by
          cases o <;> simp [Outcome.restore] at ho <;> subst ho <;> exact unique_restore _ _ hu'
        simp only [Outcome.fill]
        exact ihL σ' e rest body hf hrest this

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
theorem agree_call {p : Program} (hp : p.storeOk) {n : Nat} (ih : Ag p n) :
    AgC p (n + 1) := by
  obtain ⟨ihS, ihs, ihL, ihC⟩ := ih
  unfold AgS AgL AgC at *
  intro m σ vs
  simp only [callState, sCallState]
  cases hfind : p.find? (·.name == m) with
  | none => rfl
  | some fn =>
    simp only
    by_cases hm : fn.method = true
    · obtain ⟨⟨rest, hps, hnt⟩, hbody⟩ := hp fn (List.mem_of_find?_eq_some hfind) hm
      simp only [hm, ite_true]
      have hfree := bindParams_free rest vs hnt
      have henv : bindParams fn.params (σ :: vs) = fill σ (bindParams fn.params (.undefined :: vs)) := by
        rw [hps]; simp only [bindParams]; rw [fill_cons_this, fill_free σ _ hfree]
      have hu : Unique (bindParams fn.params (.undefined :: vs)) := by
        rw [hps]; simp only [bindParams]
        unfold Unique; simp only [List.map_cons, uniq, ite_true, bindParams_keys]
        simpa using hnt
      rw [henv, (ihS σ _ fn.body hbody hu).1]
      cases sExecStmts p n σ (bindParams fn.params (.undefined :: vs)) fn.body with
      | error e => rfl
      | ok r =>
        obtain ⟨o, σ'⟩ := r
        cases o <;> simp [Except.map, RMap, Outcome.fill, bind, Except.bind, thisOf_fill]
    · simp [hm]

/-- Fuel by fuel, the value model running in `fill σ env` gives what the store model
gives in `env` with store `σ`, its environments seen with `this` the final store. -/
theorem agree {p : Program} (hp : p.storeOk) : ∀ n : Nat,
    (∀ σ env ss, stmtsThisFree ss = true → Unique env →
      execStmts p n (fill σ env) ss = (sExecStmts p n σ env ss).map RMap ∧
      ∀ r, sExecStmts p n σ env ss = .ok r → Unique r.1.env) ∧
    (∀ σ env s, stmtThisFree s = true → Unique env →
      execStmt p n (fill σ env) s = (sExecStmt p n σ env s).map RMap ∧
      ∀ r, sExecStmt p n σ env s = .ok r → Unique r.1.env) ∧
    (∀ σ env bss body, stmtsThisFree body = true → (∀ bs ∈ bss, bs.all (·.1 != "this") = true) → Unique env →
      loop p n (fill σ env) bss body = (sLoop p n σ env bss body).map RMap ∧
      ∀ r, sLoop p n σ env bss body = .ok r → Unique r.1.env) ∧
    (∀ m σ vs, callState p n m (σ :: vs) = sCallState p n m σ vs)
  | 0 => ⟨fun _ _ _ _ _ => ⟨by simp [execStmts, sExecStmts, Except.map], by simp [sExecStmts]⟩,
      fun _ _ _ _ _ => ⟨by simp [execStmt, sExecStmt, Except.map], by simp [sExecStmt]⟩,
      fun _ _ _ _ _ _ _ => ⟨by simp [loop, sLoop, Except.map], by simp [sLoop]⟩,
      fun _ _ _ => by simp [callState, sCallState]⟩
  | n + 1 => by
    have ih : Ag p n := agree hp n
    refine ⟨agree_stmts hp ih, ?_, agree_loop hp ih, agree_call hp ih⟩
    intro σ env s
    cases s with
    | const x e => exact agree_const hp ih x e σ env
    | let_ x e => exact agree_let hp ih x e σ env
    | assign x e => exact agree_assign hp ih x e σ env
    | ret e => exact agree_ret hp ih e σ env
    | brk => exact agree_brk hp ih σ env
    | cont => exact agree_cont hp ih σ env
    | block ss => exact agree_block hp ih ss σ env
    | ite c yes no => exact agree_ite hp ih c yes no σ env
    | switch e cases => exact agree_switch hp ih e cases σ env
    | forOf x e body => exact agree_forOf hp ih x e body σ env
    | forEntries i x e body => exact agree_forEntries hp ih i x e body σ env
    | forRange i k body => exact agree_forRange hp ih i k body σ env
    | while_ c body => exact agree_while hp ih c body σ env
    | stateSet f k v => exact agree_stateSet hp ih f k v σ env
    | stateDelete f k => exact agree_stateDelete hp ih f k σ env
    | callThis m args => exact agree_callThis hp ih m args σ env

theorem Program.storeOk_of_scoped {p : Program} (h : p.scoped = true) : p.storeOk := by
  intro fn hfn hm
  unfold Program.scoped at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hh := h.2 fn hfn
  have hd : distinct fn.params = true := hh.1.1.1.1
  have hthis : fn.thisOk = true := hh.1.1.2
  have hfree : stmtsThisFree fn.body = true := hh.1.2
  unfold Function.thisOk at hthis
  simp only [hm, ite_true] at hthis
  refine ⟨?_, hfree⟩
  cases hps : fn.params with
  | nil => simp [hps] at hthis
  | cons x rest =>
    simp only [hps, List.head?_cons, Option.some.injEq, beq_iff_eq] at hthis
    subst hthis
    rw [hps] at hd
    simp only [distinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    exact ⟨rest, rfl, by simpa using hd.1⟩

/-- **The value model agrees with the store model.** For every program that passes
the static check, running a method in the value model (the object is the binding
`this`, copied into callees and back) gives exactly what running it on one object
changed in place gives: the same result and the same final state, or the same fault. -/
theorem runMethod_store (p : Program) (fuel : Nat) (m : String) (σ : JSValue) (args : List JSValue) :
    runMethod p fuel m σ args = runMethodStore p fuel m σ args := by
  unfold runMethod runMethodStore
  split
  · rename_i h; exact (agree (Program.storeOk_of_scoped h) fuel).2.2.2 m σ args
  · rfl

/-! ## Methods that change no state

A method called in an expression must have no statement that changes the state
(`Program.scoped`). In the store model such a body leaves the store as it found
it, so an expression call loses nothing by discarding the final state. -/

theorem stmtsMutate_append : ∀ (a b : List Stmt), stmtsMutate (a ++ b) = (stmtsMutate a || stmtsMutate b)
  | [], _ => by simp [stmtsMutate]
  | s :: a, b => by simp [stmtsMutate, stmtsMutate_append a b, Bool.or_assoc]

theorem casesMutate_drop : ∀ (cases : List (Option Expr × List Stmt)) (i : Nat), casesMutate cases = false →
    stmtsMutate ((cases.drop i).flatMap (·.2)) = false
  | [], _, _ => by simp [stmtsMutate]
  | (_, body) :: rest, 0, h => by
    simp only [casesMutate, Bool.or_eq_false_iff] at h
    simp only [List.drop_zero, List.flatMap_cons, stmtsMutate_append, h.1, Bool.false_or]
    simpa using casesMutate_drop rest 0 h.2
  | (_, _) :: rest, i + 1, h => by
    simp only [casesMutate, Bool.or_eq_false_iff] at h
    simpa using casesMutate_drop rest i h.2

theorem keeps_store {p : Program} : ∀ n : Nat,
    (∀ σ env ss r, stmtsMutate ss = false → sExecStmts p n σ env ss = .ok r → r.2 = σ) ∧
    (∀ σ env s r, stmtMutates s = false → sExecStmt p n σ env s = .ok r → r.2 = σ) ∧
    (∀ σ env bss body r, stmtsMutate body = false → sLoop p n σ env bss body = .ok r → r.2 = σ)
  | 0 => ⟨fun _ _ _ _ _ h => by simp [sExecStmts] at h, fun _ _ _ _ _ h => by simp [sExecStmt] at h,
      fun _ _ _ _ _ _ h => by simp [sLoop] at h⟩
  | n + 1 => by
    obtain ⟨ihS, ihs, ihL⟩ := keeps_store (p := p) n
    refine ⟨?_, ?_, ?_⟩
    · intro σ env ss r hm h
      cases ss with
      | nil => simp [sExecStmts] at h; subst h; rfl
      | cons s rest =>
        simp only [stmtsMutate, Bool.or_eq_false_iff] at hm
        simp only [sExecStmts] at h
        cases hs : sExecStmt p n σ env s with
        | error e => simp [hs, bind, Except.bind] at h
        | ok r1 =>
          obtain ⟨o, σ1⟩ := r1
          have h1 := ihs σ env s _ hm.1 hs
          simp only at h1; subst h1
          cases o <;> simp [hs, bind, Except.bind] at h
          · exact ihS _ _ rest r hm.2 h
          all_goals (subst h; rfl)
    · intro σ env s r hm h
      cases s with
      | const x e | let_ x e =>
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e <;> simp [he, bind, Except.bind, pure, Except.pure] at h
        subst h; rfl
      | ret e =>
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e <;> simp [he, bind, Except.bind, pure, Except.pure] at h
        subst h; rfl
      | assign x e =>
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e <;> simp [he, bind, Except.bind] at h
        rename_i v
        cases ha : assign x v env <;> simp [ha, pure, Except.pure] at h
        subst h; rfl
      | brk | cont => simp [sExecStmt] at h; subst h; rfl
      | stateSet _ _ _ | stateDelete _ _ | callThis _ _ => simp [stmtMutates] at hm
      | block ss =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        cases hs : sExecStmts p n σ env ss with
        | error e => simp [hs, bind, Except.bind] at h
        | ok r1 =>
          simp [hs, bind, Except.bind, pure, Except.pure] at h; subst h
          exact ihS σ env ss r1 hm hs
      | ite c yes no =>
        simp only [stmtMutates, Bool.or_eq_false_iff] at hm
        simp only [sExecStmt] at h
        cases hc : evalExpr p n (fill σ env) c with
        | error e => simp [hc, bind, Except.bind] at h
        | ok cv =>
          have bc : ∀ b, stmtsMutate b = false →
              (do let (o, σ') ← sExecStmts p n σ env b; pure (o.restore env, σ') : Except Fault _) = .ok r →
                r.2 = σ := by
            intro b hb hh
            cases hs : sExecStmts p n σ env b with
            | error e => simp [hs, bind, Except.bind] at hh
            | ok r1 =>
              simp [hs, bind, Except.bind, pure, Except.pure] at hh; subst hh; exact ihS σ env b r1 hb hs
          simp only [hc, bind, Except.bind] at h
          cases cv
          case bool b =>
            cases b
            · exact bc no hm.2 h
            · exact bc yes hm.1 h
          all_goals simp at h
      | switch e cases =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e with
        | error err => simp [he, bind, Except.bind] at h
        | ok v =>
          simp only [he, bind, Except.bind] at h
          cases hfc : findCase p n (fill σ env) v cases 0 with
          | error err => simp [hfc] at h
          | ok oi =>
            cases oi with
            | none => simp [hfc] at h; subst h; rfl
            | some i =>
              simp only [hfc] at h
              cases hs : sExecStmts p n σ env ((cases.drop i).flatMap (·.2)) with
              | error err => simp [hs] at h
              | ok r1 =>
                have := ihS σ env _ r1 (casesMutate_drop cases i hm) hs
                obtain ⟨o, σ1⟩ := r1
                simp only at this; subst this
                simp only [hs] at h
                split at h <;> simp at h <;> subst h <;> rfl
      | forOf x e body =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e with
        | error err => simp [he, bind, Except.bind] at h
        | ok v =>
          simp only [he, bind, Except.bind] at h
          split at h
          · exact ihL σ env _ body r hm h
          · simp at h
      | forEntries i x e body =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        cases he : evalExpr p n (fill σ env) e with
        | error err => simp [he, bind, Except.bind] at h
        | ok v =>
          simp only [he, bind, Except.bind] at h
          split at h
          · exact ihL σ env _ body r hm h
          · simp at h
      | forRange i k body =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        split at h
        · exact ihL σ env _ body r hm h
        · simp at h
        · simp at h
      | while_ c body =>
        simp only [stmtMutates] at hm
        simp only [sExecStmt] at h
        exact ihL σ env _ _ r (by simp [stmtsMutate, stmtMutates, hm]) h
    · intro σ env bss body r hm h
      cases bss with
      | nil => simp [sLoop] at h; subst h; rfl
      | cons bs rest =>
        simp only [sLoop] at h
        cases hs : sExecStmts p n σ (bs ++ env) body with
        | error e => simp [hs, bind, Except.bind] at h
        | ok r1 =>
          obtain ⟨o, σ1⟩ := r1
          have h1 := ihS σ _ body _ hm hs
          simp only at h1; subst h1
          simp only [hs, bind, Except.bind] at h
          split at h
          · simp at h; subst h; rfl
          · simp at h; subst h; rfl
          · exact ihL _ _ rest body r hm h
          · exact ihL _ _ rest body r hm h

/-- A method with no statement that changes the state returns the store it was given. -/
theorem sCallState_keeps {p : Program} (n : Nat) (m : String) (σ : JSValue) (vs : List JSValue)
    (hpure : ∀ fn ∈ p, fn.name = m → stmtsMutate fn.body = false) {r : JSValue × JSValue}
    (h : sCallState p n m σ vs = .ok r) : r.2 = σ := by
  cases n with
  | zero => simp [sCallState] at h
  | succ n =>
    simp only [sCallState] at h
    cases hfind : p.find? (·.name == m) with
    | none => simp [hfind] at h
    | some fn =>
      have hm := hpure fn (List.mem_of_find?_eq_some hfind) (by simpa using List.find?_some hfind)
      simp only [hfind] at h
      split at h
      · cases hs : sExecStmts p n σ (bindParams fn.params (.undefined :: vs)) fn.body with
        | error e => simp [hs, bind, Except.bind] at h
        | ok r1 =>
          have := (keeps_store n).1 σ _ fn.body r1 hm hs
          obtain ⟨o, σ1⟩ := r1
          simp only at this; subst this
          simp only [hs, bind, Except.bind] at h
          split at h <;> simp [storeOf] at h
          all_goals (rename_i heq; simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; split at h <;> simp [pure, Except.pure] at h; subst h; rename_i hh; split at hh <;> simp_all)
      · simp at h

theorem nodup_of_distinct : ∀ {xs : List String}, distinct xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [distinct, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodup_of_distinct h.2⟩

theorem eq_of_nodup_map {α β} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, he.symm⟩ h.1
    · exact absurd ⟨a, ha, he⟩ h.1
    · exact eq_of_nodup_map f h.2 ha hb he

/-- In a program that passes the static check, a method an expression may call (one
in the check's `pure` list) leaves the store as it found it: evaluating expressions
without threading the store is exact. -/
theorem scoped_pure_keeps {p : Program} (hp : p.scoped) {m : String}
    (hm : m ∈ (p.filter fun fn => fn.method && !stmtsMutate fn.body).map (·.name))
    {n : Nat} {σ : JSValue} {vs : List JSValue} {r : JSValue × JSValue}
    (h : sCallState p n m σ vs = .ok r) : r.2 = σ := by
  simp only [Program.scoped, Bool.and_eq_true] at hp
  have hd := nodup_of_distinct hp.1
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨fn0, ⟨hin0, -, hpure0⟩, rfl⟩ := hm
  refine sCallState_keeps n _ σ vs (fun fn hin hn => ?_) h
  rw [eq_of_nodup_map Function.name hd hin hin0 hn]; exact hpure0

end Ariadne

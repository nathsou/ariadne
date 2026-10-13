import V2.Proof.Expr

/-!
# Adequacy of statements

A statement list run by the model from an environment related to `ρ` converges to
an outcome related to its continuation-passing denotation: a `return` carries a
value representing the result; completing normally, `break` and `continue` leave
the list's declarations on top of an environment related to some `ρ'` where the
denotation is the corresponding continuation at `ρ'`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace V2

/-- How a list ended without returning: its declarations `bs` on top of an
environment of the starting length related to `ρ'`, where the result is `kk ρ'` and
what follows is safe. -/
def Exit {Γ : Ctx} {α : Type} (env0 env : Env) (kk : Γ.denote → α) (ks : Γ.denote → Bool) (r : α) : Prop :=
  ∃ bs envM ρ', env = bs ++ envM ∧ envM.length = env0.length ∧ EnvRel Γ envM ρ' ∧ r = kk ρ' ∧ ks ρ' = true

def SRel (Γ : Ctx) (τ : Ty) (env0 : Env) (r : τ.denote) (k : K Γ τ.denote) (ks : K Γ Bool)
    (falls breaks conts : Bool) : Outcome → Prop
  | .returned w => τ.Rep w r
  | .normal env => falls = true ∧ Exit env0 env k.normal ks.normal r
  | .broke env => breaks = true ∧ Exit env0 env k.brk ks.brk r
  | .continued env => conts = true ∧ Exit env0 env k.cont ks.cont r

/-- Discharge implications between control-flow flags. -/
macro "flags" : tactic => `(tactic| ((try intro h) <;> (try simp only [Bool.or_eq_true, Bool.and_eq_true] at *) <;>
  (try rcases h with h | ⟨h1, h2⟩) <;> (try rcases h with ⟨h1, h2⟩) <;> simp_all))

theorem TagLit.lit_value (t : TagLit) : t.lit.value = t.value := by cases t <;> rfl

/-! ## Outcomes -/

theorem Exit.restore {Γ : Ctx} {α} {env0 env : Env} {kk : Γ.denote → α} {ks r} (h : Exit env0 env kk ks r) :
    Exit env0 (V2.restore env0 env) kk ks r ∧ ∃ ρ', EnvRel Γ (V2.restore env0 env) ρ' ∧ r = kk ρ' ∧ ks ρ' = true := by
  obtain ⟨bs, envM, ρ', rfl, hl, he, hr, hk⟩ := h
  have : V2.restore env0 (bs ++ envM) = envM := by simp [V2.restore, hl]
  rw [this]
  exact ⟨⟨[], envM, ρ', rfl, hl, he, hr, hk⟩, ρ', he, hr, hk⟩

theorem SRel.restore {Γ τ env r k ks f b c o} (h : SRel Γ τ env r k ks f b c o) :
    SRel Γ τ env r k ks f b c (o.restore env) := by
  cases o with
  | returned => exact h
  | normal e => exact ⟨h.1, h.2.restore.1⟩
  | broke e => exact ⟨h.1, h.2.restore.1⟩
  | continued e => exact ⟨h.1, h.2.restore.1⟩

theorem SRel.mono {Γ τ env r k ks f b c f' b' c' o} (h : SRel Γ τ env r k ks f b c o)
    (hf : f = true → f' = true) (hb : b = true → b' = true) (hc : c = true → c' = true) :
    SRel Γ τ env r k ks f' b' c' o := by
  cases o with
  | returned => exact h
  | normal e => exact ⟨hf h.1, h.2⟩
  | broke e => exact ⟨hb h.1, h.2⟩
  | continued e => exact ⟨hc h.1, h.2⟩

theorem SRel.relen {Γ τ env env' r k ks f b c o} (h : SRel Γ τ env r k ks f b c o) (hl : env.length = env'.length) :
    SRel Γ τ env' r k ks f b c o := by
  cases o with
  | returned => exact h
  | normal e | broke e | continued e =>
    obtain ⟨hf, bs, envM, ρ', h1, h2, h3, h4, h5⟩ := h
    exact ⟨hf, bs, envM, ρ', h1, h2.trans hl, h3, h4, h5⟩

theorem Exit.pop {Γ : Ctx} {x σ} {α} {w : JSValue} {env env' : Env} {kk : Γ.denote → α} {ks r}
    (h : Exit (Γ := (x, σ) :: Γ) ((x, w) :: env) env' (kk ∘ Prod.snd) (ks ∘ Prod.snd) r) : Exit env env' kk ks r := by
  obtain ⟨bs, envM, ⟨a, ρ'⟩, rfl, hl, ⟨w', envM', rfl, _, he⟩, hr, hk⟩ := h
  exact ⟨bs ++ [(x, w')], envM', ρ', by simp, by simpa using hl, he, hr, hk⟩

/-- Leaving a declaration's scope. -/
theorem SRel.pop {Γ x σ τ w env r k ks f b c o}
    (h : SRel ((x, σ) :: Γ) τ ((x, w) :: env) r (k.map Prod.snd) (ks.map Prod.snd) f b c o) :
    SRel Γ τ env r k ks f b c o := by
  cases o with
  | returned => exact h
  | normal e | broke e | continued e => exact ⟨h.1, h.2.pop⟩

/-- Leaving a narrowed context. -/
theorem SRel.widen {Γ τ x τ0 σ} {v : Var Γ x τ0} {e : σ.denote → τ0.denote} {env r k ks f b c o}
    (he : ∀ w y, σ.Rep w y → τ0.Rep w (e y))
    (h : SRel (v.narrow σ) τ env r (k.map (v.widen e)) (ks.map (v.widen e)) f b c o) :
    SRel Γ τ env r k ks f b c o := by
  cases o with
  | returned => exact h
  | normal _ | broke _ | continued _ =>
    obtain ⟨hf, bs, envM, ρ', h1, h2, h3, h4, h5⟩ := h
    exact ⟨hf, bs, envM, v.widen e ρ', h1, h2, v.widenRel e he h3, h4, h5⟩

/-- The outcome of a `switch`: a `break` aimed at it completes it normally. -/
def switchOutcome : Outcome → Outcome
  | .broke env => .normal env
  | o => o

theorem SRel.switch {Γ τ env r} {k : K Γ τ.denote} {ks : K Γ Bool} {R RS f b c o}
    (h : SRel Γ τ env r { k with normal := R, brk := R } { ks with normal := RS, brk := RS } f b c o) :
    SRel Γ τ env r { k with normal := R } { ks with normal := RS } (f || b) false c (switchOutcome o) := by
  cases o with
  | returned => exact h
  | normal e => exact ⟨by simp [h.1], h.2⟩
  | broke e => exact ⟨by simp [h.1], h.2⟩
  | continued e => exact h

/-! ## Fuel -/

section
variable {prog : Program}

theorem conv_cons_normal {s : Stmt} {rest : List Stmt} {env env' : Env} {o : Outcome}
    (h1 : Converges (fun n => execStmt prog n env s) (.ok (.normal env')))
    (h2 : Converges (fun n => execStmts prog n env' rest) (.ok o)) :
    Converges (fun n => execStmts prog n env (s :: rest)) (.ok o) := by
  obtain ⟨N1, h1⟩ := h1
  obtain ⟨N2, h2⟩ := h2
  exact Converges.of_succ (max N1 N2) fun m hm => by
    simp [execStmts, h1 m (by omega), h2 m (by omega), bind, Except.bind]

theorem conv_cons_exit {s : Stmt} {rest : List Stmt} {env : Env} {o : Outcome}
    (h1 : Converges (fun n => execStmt prog n env s) (.ok o)) (h : ∀ e, o ≠ .normal e) :
    Converges (fun n => execStmts prog n env (s :: rest)) (.ok o) := by
  obtain ⟨N1, h1⟩ := h1
  exact Converges.of_succ N1 fun m hm => by
    cases o with
    | normal e => exact absurd rfl (h e)
    | _ => simp [execStmts, h1 m hm, bind, Except.bind]

/-- A statement followed by the rest of its list. -/
theorem conv_seq {s : Stmt} {rest : List Stmt} {env : Env} {o out : Outcome}
    (h1 : Converges (fun n => execStmt prog n env s) (.ok o))
    (h2 : ∀ e, o = .normal e → Converges (fun n => execStmts prog n e rest) (.ok out))
    (h3 : ∀ e, o ≠ .normal e → out = o) :
    Converges (fun n => execStmts prog n env (s :: rest)) (.ok out) := by
  cases o with
  | normal e => exact conv_cons_normal h1 (h2 e rfl)
  | _ => rw [h3 [] (by simp)]; exact conv_cons_exit h1 (by simp)

theorem execStmts_append : ∀ (m : Nat) (env : Env) (A B : List Stmt) (o : Outcome),
    execStmts prog m env A = .ok o → (∀ e, o ≠ .normal e) → execStmts prog m env (A ++ B) = .ok o
  | 0, _, _, _, _, h, _ => by simp [execStmts] at h
  | _ + 1, env, [], _, o, h, hn => by simp [execStmts] at h; subst h; exact absurd rfl (hn env)
  | m + 1, env, s :: A, B, o, h, hn => by
    simp only [execStmts, List.cons_append, bind, Except.bind] at h ⊢
    cases hs : execStmt prog m env s with
    | error e => simp [hs] at h
    | ok o' =>
      simp only [hs] at h ⊢
      cases o' with
      | normal e => exact execStmts_append m e A B o h hn
      | _ => exact h

theorem conv_append {env : Env} {A B : List Stmt} {o : Outcome}
    (h : Converges (fun n => execStmts prog n env A) (.ok o)) (hn : ∀ e, o ≠ .normal e) :
    Converges (fun n => execStmts prog n env (A ++ B)) (.ok o) := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun m hm => execStmts_append m env A B o (h m hm) hn⟩

theorem conv_ite {c : Expr} {yes no : List Stmt} {env : Env} {b : Bool} {o : Outcome}
    (hc : Converges (fun n => evalExpr prog n env c) (.ok (.bool b)))
    (hb : Converges (fun n => execStmts prog n env (if b then yes else no)) (.ok o)) :
    Converges (fun n => execStmt prog n env (.ite c yes no)) (.ok (o.restore env)) := by
  obtain ⟨Nc, hc⟩ := hc
  obtain ⟨Nb, hb⟩ := hb
  refine Converges.of_succ (max Nc Nb) fun m hm => ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb
    simp [execStmt, hc m (by omega), hb m (by omega), bind, Except.bind, pure, Except.pure]
  · simp only [↓reduceIte] at hb
    simp [execStmt, hc m (by omega), hb m (by omega), bind, Except.bind, pure, Except.pure]

theorem conv_block {ss : List Stmt} {env : Env} {o : Outcome}
    (hb : Converges (fun n => execStmts prog n env ss) (.ok o)) :
    Converges (fun n => execStmt prog n env (.block ss)) (.ok (o.restore env)) := by
  obtain ⟨Nb, hb⟩ := hb
  exact Converges.of_succ Nb fun m hm => by
    simp [execStmt, hb m hm, bind, Except.bind, pure, Except.pure]

end

/-! ## Tags -/

theorem TagLit.strictEq_value {a b : TagLit} (h : a.isStr = b.isStr) :
    strictEq a.value b.value = .ok (decide (a = b)) := by
  cases a with
  | str s => cases b with
    | str s' => by_cases hs : s = s' <;> simp [TagLit.value, strictEq, hs]
    | bool _ => simp [TagLit.isStr] at h
  | bool c => cases b with
    | bool c' => by_cases hs : c = c' <;> simp [TagLit.value, strictEq, hs]
    | str _ => simp [TagLit.isStr] at h

/-- A union value's tag is one of the union's tags. -/
theorem Variants.rep_tag : ∀ {vs : Variants} {key kvs} {u : vs.denote}, vs.Rep key kvs u →
    ∃ t ∈ vs.tags, fieldOf kvs key = t.value
  | .one t _, _, _, _, ⟨h, _⟩ => ⟨t, by simp [Variants.tags], h⟩
  | .cons t _ _, _, _, .inl _, ⟨h, _⟩ => ⟨t, by simp [Variants.tags], h⟩
  | .cons _ _ rest, _, _, .inr _, h => by
    obtain ⟨t, ht, h⟩ := Variants.rep_tag (vs := rest) h
    exact ⟨t, by simp [Variants.tags, ht], h⟩

theorem Variants.tagsOk_cons {t : TagLit} {fs : Fields} {rest : Variants} (h : (Variants.cons t fs rest).tagsOk = true) :
    rest.tagsOk = true ∧ t ∉ rest.tags ∧ ∀ t' ∈ rest.tags, t'.isStr = t.isStr := by
  simp only [Variants.tagsOk, Variants.tags, Bool.and_eq_true, Bool.or_eq_true, List.all_cons,
    Variants.tagsOk.distinctTagList, Bool.not_eq_true'] at h
  obtain ⟨hk, hc, hd⟩ := h
  refine ⟨?_, by simpa using hc, ?_⟩
  · simp only [Variants.tagsOk, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨?_, hd⟩
    rcases hk with ⟨_, h⟩ | ⟨_, h⟩
    · exact .inl h
    · exact .inr h
  · intro t' ht'
    rcases hk with ⟨h1, h⟩ | ⟨h1, h⟩
    · have := List.all_eq_true.mp h t' ht'; simp_all
    · have := List.all_eq_true.mp h t' ht'; cases t <;> cases t' <;> simp_all [TagLit.isStr]

theorem Variants.tagsOk_mem {vs : Variants} (h : vs.tagsOk = true) {a b : TagLit} (ha : a ∈ vs.tags)
    (hb : b ∈ vs.tags) : a.isStr = b.isStr := by
  simp only [Variants.tagsOk, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.1 with h | h
  · rw [List.all_eq_true.mp h a ha, List.all_eq_true.mp h b hb]
  · have h1 := List.all_eq_true.mp h a ha
    have h2 := List.all_eq_true.mp h b hb
    simp at h1 h2; rw [h1, h2]

theorem Variants.head_mem {t : TagLit} {fs : Fields} {rest : Variants} : t ∈ (Variants.cons t fs rest).tags := by
  simp [Variants.tags]

theorem Variants.one_mem {t : TagLit} {fs : Fields} : t ∈ (Variants.one t fs).tags := by
  simp [Variants.tags]

/-- A variant's record represents the narrowed variable. -/
theorem vrec_rep {key t fs kvs} {y : fs.denote} (hn : (kvs.map Prod.fst).Nodup) (ht : fieldOf kvs key = t.value)
    (hy : fs.Rep kvs y) : (vrec key t fs).Rep (.record kvs) ((), y) :=
  ⟨kvs, rfl, hn, ht, hy⟩

/-! ## The induction -/

theorem SRel.restore_len {Γ τ env r k ks f b c o} (h : SRel Γ τ env r k ks f b c o) :
    ∀ e, o.restore env = .normal e → e.length = env.length := by
  intro e he
  cases o with
  | normal e0 =>
    simp only [Outcome.restore, Outcome.normal.injEq] at he; subst he
    obtain ⟨-, bs, envM, _, rfl, hl, -⟩ := h
    simp [V2.restore, hl]
  | _ => simp [Outcome.restore] at he

theorem switchOutcome_len {env : Env} {o : Outcome} (h : ∀ e, o.restore env = .normal e → e.length = env.length)
    (hb : ∀ e, o.restore env = .broke e → e.length = env.length) :
    ∀ e, switchOutcome (o.restore env) = .normal e → e.length = env.length := by
  intro e he
  cases ho : o.restore env with
  | normal e' => rw [ho] at he; simp [switchOutcome] at he; subst he; exact h e' ho
  | broke e' => rw [ho] at he; simp [switchOutcome] at he; subst he; exact hb e' ho
  | _ => rw [ho] at he; simp [switchOutcome] at he

theorem SRel.restore_len_broke {Γ τ env r k ks f b c o} (h : SRel Γ τ env r k ks f b c o) :
    ∀ e, o.restore env = .broke e → e.length = env.length := by
  intro e he
  cases o with
  | broke e0 =>
    simp only [Outcome.restore, Outcome.broke.injEq] at he; subst he
    obtain ⟨-, bs, envM, _, rfl, hl, -⟩ := h
    simp [V2.restore, hl]
  | _ => simp [Outcome.restore] at he

theorem conv_switch {prog : Program} {d : Expr} {cases : List (Option Expr × List Stmt)} {env : Env} {v : JSValue}
    {j : Nat} {o : Outcome}
    (hd : Converges (fun n => evalExpr prog n env d) (.ok v))
    (hf : Converges (fun n => findCase prog n env v cases 0) (.ok (some j)))
    (hb : Converges (fun n => execStmts prog n env ((cases.drop j).flatMap (·.2))) (.ok o)) :
    Converges (fun n => execStmt prog n env (.switch d cases)) (.ok (switchOutcome (o.restore env))) := by
  obtain ⟨Nd, hd⟩ := hd
  obtain ⟨Nf, hf⟩ := hf
  obtain ⟨Nb, hb⟩ := hb
  refine Converges.of_succ (max Nd (max Nf Nb)) fun m hm => ?_
  simp only [execStmt, hd m (by omega), hf m (by omega), hb m (by omega), bind, Except.bind]
  cases o.restore env <;> rfl

theorem conv_const {prog : Program} {e : Expr} {x : String} {env : Env} {w : JSValue}
    (h : Converges (fun n => evalExpr prog n env e) (.ok w)) :
    Converges (fun n => execStmt prog n env (.const x e)) (.ok (.normal ((x, w) :: env))) := by
  obtain ⟨N, h⟩ := h
  exact Converges.of_succ N fun m hm => by simp [execStmt, h m hm, bind, Except.bind, pure, Except.pure]

theorem conv_ret {prog : Program} {e : Expr} {env : Env} {w : JSValue}
    (h : Converges (fun n => evalExpr prog n env e) (.ok w)) :
    Converges (fun n => execStmt prog n env (.ret e)) (.ok (.returned w)) := by
  obtain ⟨N, h⟩ := h
  exact Converges.of_succ N fun m hm => by simp [execStmt, h m hm, bind, Except.bind, pure, Except.pure]

theorem conv_brk {prog : Program} {env : Env} : Converges (fun n => execStmt prog n env .brk) (.ok (.broke env)) :=
  Converges.of_succ 0 fun m _ => by simp [execStmt]

theorem conv_nil {prog : Program} {env : Env} : Converges (fun n => execStmts prog n env []) (.ok (.normal env)) :=
  Converges.of_succ 0 fun m _ => by simp [execStmts]

/-- A branch in a context narrowed by `x != null`. -/
theorem some_embed {σ : Ty} {n : Nullish} : ∀ w (y : σ.denote), σ.Rep w y → (Ty.option n σ).Rep w (some y) :=
  fun _ _ h => h

section
variable {prog : Program} {Φ : Sigs} {fs : Φ.denote} {ss : Φ.safety} (hfs : FnsOK prog fs ss)
include hfs

/-- A compound statement, then the rest of its list as its normal continuation. -/
theorem then_rest {Γ τ} {s : Stmt} {rest : TStmts Φ Γ τ} {k : K Γ τ.denote} {ks : K Γ Bool} {env : Env}
    {r : τ.denote} {o : Outcome} {f b c : Bool}
    (hrest : ∀ envM ρ', envM.length = env.length → EnvRel Γ envM ρ' → rest.safe fs ss ks ρ' = true →
      ∃ o2, Converges (fun n => execStmts prog n envM rest.erase) (.ok o2) ∧
        SRel Γ τ envM (rest.denote fs k ρ') k ks rest.falls rest.breaks rest.continues o2)
    (h1 : Converges (fun n => execStmt prog n env s) (.ok o))
    (ho : SRel Γ τ env r { k with normal := rest.denote fs k } { ks with normal := rest.safe fs ss ks } f b c o)
    (hlen : ∀ e, o = .normal e → e.length = env.length) :
    ∃ out, Converges (fun n => execStmts prog n env (s :: rest.erase)) (.ok out) ∧
      SRel Γ τ env r k ks (f && rest.falls) (b || (f && rest.breaks)) (c || (f && rest.continues)) out := by
  cases o with
  | normal e =>
    obtain ⟨hf, bs, envM, ρ', rfl, hl, hrel, hr, hsafe⟩ := ho
    have hbs : bs = [] := by
      have h' := hlen _ rfl
      rw [List.length_append, hl] at h'
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    obtain ⟨o2, hc2, hr2⟩ := hrest envM ρ' hl hrel hsafe
    refine ⟨o2, conv_cons_normal h1 hc2, ?_⟩
    rw [hr]
    exact (hr2.relen hl).mono (by simp [hf]) (by simp [hf]; exact .inr) (by simp [hf]; exact .inr)
  | returned w => exact ⟨_, conv_cons_exit h1 (by simp), ho⟩
  | broke e => exact ⟨_, conv_cons_exit h1 (by simp), by simp [ho.1], ho.2⟩
  | continued e => exact ⟨_, conv_cons_exit h1 (by simp), by simp [ho.1], ho.2⟩

mutual
  theorem TStmts.adequate : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (k : K Γ τ.denote) (ks : K Γ Bool)
      {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ → st.safe fs ss ks ρ = true → st.wf = true →
      ∃ out, Converges (fun n => execStmts prog n env st.erase) (.ok out) ∧
        SRel Γ τ env (st.denote fs k ρ) k ks st.falls st.breaks st.continues out
    | _, _, .nil, k, ks, env, ρ, he, hs, _ =>
      ⟨_, conv_nil, rfl, [], env, ρ, rfl, rfl, he, rfl, hs⟩
    | _, _, .const x e rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.safe, Bool.and_eq_true] at hs
      obtain ⟨w, hc, hrep⟩ := TExpr.adequate hfs e he hs.1
      obtain ⟨o, hc2, hr⟩ := TStmts.adequate rest (k.map Prod.snd) (ks.map Prod.snd)
        (env := (x, w) :: env) (ρ := (e.denote fs ρ, ρ)) ⟨w, env, rfl, hrep, he⟩ hs.2 hw
      exact ⟨o, conv_cons_normal (conv_const hc) hc2, hr.pop⟩
    | _, _, .ret e rest, k, ks, env, ρ, he, hs, _ => by
      obtain ⟨w, hc, hrep⟩ := TExpr.adequate hfs e he hs
      exact ⟨_, conv_cons_exit (conv_ret hc) (by simp), hrep⟩
    | _, _, .brk rest, k, ks, env, ρ, he, hs, _ =>
      ⟨_, conv_cons_exit conv_brk (by simp), rfl, [], env, ρ, rfl, rfl, he, rfl, hs⟩
    | Γ, τ, .ite c yes no rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.safe, Bool.and_eq_true] at hs
      simp only [TStmts.wf, Bool.and_eq_true] at hw
      obtain ⟨wc, hcc, hwc⟩ := TExpr.adequate hfs c he hs.1
      simp only [Ty.Rep] at hwc; subst hwc
      have hrest := fun envM ρ' (_ : envM.length = env.length) hrel hsafe =>
        TStmts.adequate rest k ks (env := envM) (ρ := ρ') hrel hsafe hw.2
      cases hb : c.denote fs ρ
      · simp only [hb] at hs hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate no { k with normal := rest.denote fs k }
          { ks with normal := rest.safe fs ss ks } he (by simpa using hs.2) hw.1.2
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro.restore hro.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hb, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
      · simp only [hb] at hs hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate yes { k with normal := rest.denote fs k }
          { ks with normal := rest.safe fs ss ks } he (by simpa using hs.2) hw.1.1
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro.restore hro.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hb, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
    | Γ, τ, .block body rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.wf, Bool.and_eq_true] at hw
      have hrest := fun envM ρ' (_ : envM.length = env.length) hrel hsafe =>
        TStmts.adequate rest k ks (env := envM) (ρ := ρ') hrel hsafe hw.2
      obtain ⟨o, hco, hro⟩ := TStmts.adequate body { k with normal := rest.denote fs k }
        { ks with normal := rest.safe fs ss ks } he hs hw.1
      exact then_rest hfs hrest (conv_block hco) hro.restore hro.restore_len
    | Γ, τ, .ifNull v hσ yes no rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.wf, Bool.and_eq_true] at hw
      have hcc := nullTest_converges hfs v hσ he
      have hrest := fun envM ρ' (_ : envM.length = env.length) hrel hsafe =>
        TStmts.adequate rest k ks (env := envM) (ρ := ρ') hrel hsafe hw.2
      cases hx : v.get ρ with
      | none =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isNone_none] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate yes { k with normal := rest.denote fs k }
          { ks with normal := rest.safe fs ss ks } he hs hw.1.1
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro.restore hro.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
      | some y =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isNone_some] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate no (K.map (v.widen some) { k with normal := rest.denote fs k })
          (K.map (v.widen some) { ks with normal := rest.safe fs ss ks }) (narrow_some hfs v he hx) hs hw.1.2
        have hro' := SRel.widen some_embed hro
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro'.restore
          hro'.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
    | Γ, τ, .ifNotNull v hσ yes no rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.wf, Bool.and_eq_true] at hw
      have hcc := notNullTest_converges hfs v hσ he
      have hrest := fun envM ρ' (_ : envM.length = env.length) hrel hsafe =>
        TStmts.adequate rest k ks (env := envM) (ρ := ρ') hrel hsafe hw.2
      cases hx : v.get ρ with
      | none =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isSome_none] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate no { k with normal := rest.denote fs k }
          { ks with normal := rest.safe fs ss ks } he hs hw.1.2
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro.restore hro.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
      | some y =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isSome_some] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate yes (K.map (v.widen some) { k with normal := rest.denote fs k })
          (K.map (v.widen some) { ks with normal := rest.safe fs ss ks }) (narrow_some hfs v he hx) hs hw.1.1
        have hro' := SRel.widen some_embed hro
        obtain ⟨out, h, hr⟩ := then_rest hfs hrest (conv_ite hcc (by simpa using hco)) hro'.restore
          hro'.restore_len
        refine ⟨out, h, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hr.mono (by flags) (by flags) (by flags)
    | Γ, τ, .ifNullExit (x := x) v hσ yes rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
      have hcc := nullTest_converges hfs v hσ he
      cases hx : v.get ρ with
      | none =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isNone_none] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate yes k ks he hs hw.1.2
        have hn : ∀ e, o.restore env ≠ .normal e := by
          intro e he'; cases o with
          | normal _ => simp [SRel, hw.1.1] at hro
          | _ => simp [Outcome.restore] at he'
        refine ⟨_, conv_cons_exit (conv_ite hcc (by simpa using hco)) hn, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact hro.restore.mono (by flags) (by flags) (by flags)
      | some y =>
        simp only [TStmts.safe, hx] at hs
        simp only [hx, Option.isNone_some] at hcc
        obtain ⟨o, hco, hro⟩ := TStmts.adequate rest (k.map (v.widen some)) (ks.map (v.widen some))
          (narrow_some hfs v he hx) hs hw.2
        have hite : Converges (fun n => execStmt prog n env (.ite (nullTest x) yes.erase [])) (.ok (.normal env)) := by
          have := conv_ite hcc (yes := yes.erase) (no := []) (by simpa using conv_nil (prog := prog) (env := env))
          simpa [Outcome.restore, V2.restore] using this
        refine ⟨o, conv_cons_normal hite hco, ?_⟩
        simp only [TStmts.denote, hx, TStmts.falls, TStmts.breaks, TStmts.continues]
        exact (SRel.widen some_embed hro).mono (by flags) (by flags) (by flags)
    | Γ, τ, .switchU (x := x) (key := key) (vs := vs) v hok cases rest, k, ks, env, ρ, he, hs, hw => by
      simp only [TStmts.wf, Bool.and_eq_true] at hw
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      have hrest := fun envM ρ' (_ : envM.length = env.length) hrel hsafe =>
        TStmts.adequate rest k ks (env := envM) (ρ := ρ') hrel hsafe hw.2
      obtain ⟨w, hl, kvs, rfl, hnd, hrep⟩ := v.lookup he
      have hd : Converges (fun n => evalExpr prog n env (.field (.var x) key)) (.ok (fieldOf kvs key)) :=
        Converges.of_succ 1 fun m hm => by
          obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          simp [evalExpr, hl, bind, Except.bind, getField_record hok.2]
      obtain ⟨j, o, hf, hb, hro⟩ := TCases.adequate cases { k with normal := rest.denote fs k, brk := rest.denote fs k }
        { ks with normal := rest.safe fs ss ks, brk := rest.safe fs ss ks } id (v.get ρ) kvs 0 he hl hnd hrep
        (fun _ _ _ h => h) hok.1 hs hw.1
      simp only [Nat.zero_add] at hf
      have hsw := conv_switch hd hf hb
      have hro' := hro.restore.switch
      obtain ⟨out, h, hr⟩ := then_rest hfs hrest hsw hro'
        (switchOutcome_len hro.restore_len hro.restore_len_broke)
      refine ⟨out, h, ?_⟩
      simp only [TStmts.denote, TStmts.falls, TStmts.breaks, TStmts.continues]
      exact hr.mono (by flags) (by flags) (by flags)

  theorem TCases.adequate {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ {vs : Variants} (cases : TCases Φ Γ τ v vs) (k : K Γ τ.denote) (ks : K Γ Bool) {env : Env}
        {ρ : Γ.denote} (inj : vs.denote → vs0.denote) (u : vs.denote) (kvs : List (String × JSValue)) (i0 : Nat),
        EnvRel Γ env ρ → env.lookup x = some (.record kvs) → (kvs.map Prod.fst).Nodup → vs.Rep key kvs u →
        (∀ kvs' u', (kvs'.map Prod.fst).Nodup → vs.Rep key kvs' u' → vs0.Rep key kvs' (inj u')) →
        vs.tagsOk = true → cases.safe fs ss ks ρ inj u = true → cases.wf = true →
        ∃ j out, Converges (fun n => findCase prog n env (fieldOf kvs key) cases.erase i0) (.ok (some (i0 + j))) ∧
          Converges (fun n => execStmts prog n env ((cases.erase.drop j).flatMap (·.2))) (.ok out) ∧
          SRel Γ τ env (cases.denote fs k ρ inj u) k ks cases.falls cases.breaks cases.continues out
    | .one t fs', .one body, k, ks, env, ρ, inj, u, kvs, i0, he, hl, hnd, hrep, hinj, hok, hs, hw => by
      obtain ⟨ht, hu⟩ := hrep
      have hrel : EnvRel (v.narrow (vrec key t fs')) env (v.narrowVal ρ ((), u)) :=
        v.narrowRel he fun w hw _ => by rw [hl] at hw; cases hw; exact vrec_rep hnd ht hu
      obtain ⟨o, hco, hro⟩ := TStmts.adequate body (k.map (v.widen fun z => inj z.2))
        (ks.map (v.widen fun z => inj z.2)) hrel hs hw
      refine ⟨0, o, Converges.of_succ 1 fun m hm => ?_, by simpa [TCases.erase] using hco, ?_⟩
      · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp [findCase, TCases.erase, evalExpr, ht, TagLit.lit_value, bind, Except.bind, pure, Except.pure,
          TagLit.strictEq_value (a := t) (b := t) rfl]
      · refine SRel.widen (fun w z hz => ?_) hro
        obtain ⟨kvs', rfl, hnd', ht', hz'⟩ := hz
        exact ⟨kvs', rfl, hnd', hinj kvs' _ hnd' ⟨ht', hz'⟩⟩
    | .cons t fs' more, .cons body rest, k, ks, env, ρ, inj, u, kvs, i0, he, hl, hnd, hrep, hinj, hok, hs, hw => by
      simp only [TCases.wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
      have hok' := Variants.tagsOk_cons hok
      cases u with
      | inl y =>
        obtain ⟨ht, hu⟩ := hrep
        have hrel : EnvRel (v.narrow (vrec key t fs')) env (v.narrowVal ρ ((), y)) :=
          v.narrowRel he fun w hw _ => by rw [hl] at hw; cases hw; exact vrec_rep hnd ht hu
        obtain ⟨o, hco, hro⟩ := TStmts.adequate body (k.map (v.widen fun z => inj (.inl z.2)))
          (ks.map (v.widen fun z => inj (.inl z.2))) hrel hs hw.1.2
        have hn : ∀ e, o ≠ .normal e := by
          intro e h; subst h; simp [SRel, hw.1.1] at hro
        refine ⟨0, o, Converges.of_succ 1 fun m hm => ?_, by simpa [TCases.erase] using conv_append hco hn, ?_⟩
        · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          simp [findCase, TCases.erase, evalExpr, ht, TagLit.lit_value, bind, Except.bind, pure, Except.pure,
            TagLit.strictEq_value (a := t) (b := t) rfl]
        · have := SRel.widen (fun w z hz => by
            obtain ⟨kvs', rfl, hnd', ht', hz'⟩ := hz
            exact ⟨kvs', rfl, hnd', hinj kvs' _ hnd' ⟨ht', hz'⟩⟩) hro
          simp only [TCases.denote, TCases.falls, TCases.breaks, TCases.continues]
          exact this.mono (by flags) (by flags) (by flags)
      | inr w =>
        obtain ⟨t', ht', hfield⟩ := Variants.rep_tag (vs := more) hrep
        have hne : t' ≠ t := fun h => hok'.2.1 (h ▸ ht')
        obtain ⟨j, o, hf, hb, hro⟩ := TCases.adequate rest k ks (fun z => inj (.inr z)) w kvs (i0 + 1) he hl hnd
          hrep (fun kvs' u' hn' h => hinj kvs' (.inr u') hn' h) hok'.1 hs hw.2
        refine ⟨j + 1, o, ?_, by simpa [TCases.erase] using hb, ?_⟩
        · obtain ⟨N, hf⟩ := hf
          refine Converges.of_succ (N + 1) fun m hm => ?_
          obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          have hf' := hf (m' + 1) (by omega)
          simp only [hfield] at hf'
          have hj : i0 + 1 + j = i0 + (j + 1) := by omega
          simp [findCase, TCases.erase, evalExpr, hfield, TagLit.lit_value, bind, Except.bind, pure, Except.pure,
            TagLit.strictEq_value (hok'.2.2 t' ht'), hne, hf', hj]
        · simp only [TCases.denote, TCases.falls, TCases.breaks, TCases.continues]
          exact hro.mono (by flags) (by flags) (by flags)
end

end

end V2

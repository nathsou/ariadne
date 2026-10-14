import V2.Proof.Safe
import V2.Eqns.Denote
import V2.Eqns.Erase

/-!
# Adequacy of expressions

Every safe typed expression, evaluated by the model in an environment related to
`ρ`, converges to a value representing its denotation.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace V2

/-- The functions in scope, called on arguments representing safe inputs, converge
to values representing their denotations. -/
structure FnsOK {Φ : Sigs} (prog : Program) (fs : Φ.denote) (ss : Φ.safety) : Prop where
  conv : ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote) (vs : List JSValue), s.void = false →
    ArgsRep s.params vs xs → v.safe ss xs = true →
      ∃ w, Converges (fun n => call prog n f vs) (.ok w) ∧ s.result.Rep w (v.get fs xs)
  /-- Methods that change the state leave a state representing their denotation. -/
  convState : ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote) (vs : List JSValue), s.void = true →
    ArgsRep s.params vs xs → v.safe ss xs = true →
      ∃ w t, Converges (fun n => callState prog n f vs) (.ok (w, t)) ∧ s.result.Rep t (v.get fs xs)
  /-- Each function in scope is declared in the program (so its name evaluates to it). -/
  mem : ∀ {f s} (_v : FVar Φ f s), prog.any (·.name == f) = true

theorem EnvRel.lookup_none : ∀ {Γ : Ctx} {env : Env} {ρ : Γ.denote} {f : String}, EnvRel Γ env ρ →
    (Γ.map Prod.fst).contains f = false → env.lookup f = none
  | [], _, _, _, h, _ => by simp [EnvRel] at h; subst h; rfl
  | (x, _) :: _, _, (_, _), f, ⟨_, _, rfl, _, rest⟩, hf => by
    simp only [List.map, List.contains_cons, Bool.or_eq_false_iff] at hf
    have hx : f ≠ x := fun h => by subst h; simp at hf
    have : (f == x) = false := beq_eq_false_iff_ne.mpr hx
    simp [List.lookup, this, rest.lookup_none hf.2]

theorem ArgsRep.omitted : ∀ {ps : Ctx}, ps.omittable = true → ArgsRep ps [] (Ctx.none ps)
  | [], _ => rfl
  | (_, .option n _) :: ps, h => by
    simp only [Ctx.omittable, Bool.and_eq_true] at h
    refine ⟨.undefined, _, rfl, ?_, ArgsRep.omitted h.2⟩
    cases n <;> simp_all [Nullish.undef?, Ty.Rep, Nullish.admits]
  | (_, .bool) :: _, h | (_, .int) :: _, h | (_, .number) :: _, h | (_, .string) :: _, h
  | (_, .tag _) :: _, h | (_, .lits _ _) :: _, h | (_, .record _) :: _, h | (_, .union _ _) :: _, h
  | (_, .array _) :: _, h => by simp [Ctx.omittable] at h

theorem Nullish.admits_undef {n : Nullish} (h : n.undef? = true) : n.admits .undefined := by
  cases n <;> simp_all [Nullish.undef?, Nullish.admits]

theorem Nullish.admits_null {n : Nullish} (h : n.null? = true) : n.admits .null := by
  cases n <;> simp_all [Nullish.null?, Nullish.admits]

theorem Sel.rep : ∀ {fs : Fields} (sel : Sel src fs) {kvs : List (String × JSValue)} {xs : src.denote},
    kvs.map Prod.fst = src.names → src.Rep kvs xs → fs.Rep kvs (sel.pick xs)
  | .nil, .nil, _, _, _, _ => trivial
  | .cons _ _ _, .cons i rest, _, _, hn, h => ⟨i.rep h, rest.rep hn h⟩
  | .cons f _ _, .absent ha rest, kvs, _, hn, h => by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    refine ⟨?_, rest.rep hn h⟩
    have hf : f ∉ kvs.map Prod.fst := by rw [hn]; simpa using ha.2
    simp only [Ty.Rep, fieldOf, lookup_eq_none_of_not_mem hf, Option.getD_none]
    exact Nullish.admits_undef ha.1

theorem Upd.rep : ∀ {fs : Fields} (u : Upd src fs) {ps rkvs} {xs : src.denote} {r : fs.denote},
    (ps.map Prod.fst) = src.names → (ps.map Prod.fst).Nodup → src.Rep ps xs → fs.Rep rkvs r →
    fs.Rep (upsertAll rkvs ps) (u.apply xs r)
  | .nil, .nil, _, _, _, _, _, _, _, _ => trivial
  | .cons f _ _, .set i rest, ps, rkvs, xs, (_, r), hn, hd, hs, ⟨_, hr⟩ => by
    refine ⟨?_, rest.rep hn hd hs hr⟩
    have hf : f ∈ ps.map Prod.fst := by rw [hn]; exact i.mem
    rw [fieldOf_upsertAll _ _ _ hd]; simp only [hf, ↓reduceIte]
    exact i.rep hs
  | .cons f _ _, .keep h rest, ps, rkvs, xs, (_, r), hn, hd, hs, ⟨ha, hr⟩ => by
    refine ⟨?_, rest.rep hn hd hs hr⟩
    have hf : f ∉ ps.map Prod.fst := by rw [hn]; simpa using h
    rw [fieldOf_upsertAll _ _ _ hd]; simp only [hf, ↓reduceIte]
    exact ha

theorem Op.guard_elim (op : Op σ τ) {s : Bool} {x y : σ.denote} (h : op.guard s x y = true) : s = true := by
  cases op <;> simp_all [Op.guard]

/-- An operator applied to values representing its operands gives a value
representing its result, when its safety condition holds. -/
theorem Op.sound (op : Op σ τ) {wa wb : JSValue} {x y : σ.denote} {s : Bool} (ha : σ.Rep wa x) (hb : σ.Rep wb y)
    (hg : op.guard s x y = true) : ∃ w, binary op.js wa wb = .ok w ∧ τ.Rep w (op.apply x y) := by
  cases op with
  | eq hp => exact ⟨.bool (Ty.beq _ x y), by simp [Op.js, Op.apply, binary, Ty.strictEq_rep hp ha hb, bind, Except.bind, pure, Except.pure], rfl⟩
  | ne hp => exact ⟨.bool (!Ty.beq _ x y), by simp [Op.js, Op.apply, binary, Ty.strictEq_rep hp ha hb, bind, Except.bind, pure, Except.pure], rfl⟩
  | nadd | nsub | nmul =>
    simp only [Ty.Rep] at ha hb; subst ha; subst hb
    simp only [Op.guard, Bool.and_eq_true] at hg
    exact ⟨_, number_ok hg.2, rfl⟩
  | _ => simp only [Ty.Rep] at ha hb; subst ha; subst hb; exact ⟨_, rfl, rfl⟩

/-- A binary operation whose operands converge. -/
theorem converges_binary {prog : Program} {env : Env} {op : BinOp} {a b : Expr} {x y r : JSValue}
    (hop : op ≠ .and ∧ op ≠ .or ∧ op ≠ .coalesce)
    (ha : Converges (fun n => evalExpr prog n env a) (.ok x))
    (hb : Converges (fun n => evalExpr prog n env b) (.ok y))
    (hr : binary op x y = .ok r) :
    Converges (fun n => evalExpr prog n env (.binary op a b)) (.ok r) := by
  obtain ⟨Na, ha⟩ := ha
  obtain ⟨Nb, hb⟩ := hb
  refine Converges.of_succ (max Na Nb) fun m hm => ?_
  rcases op <;> simp_all [evalExpr, ha m (by omega), hb m (by omega), bind, Except.bind]

/-- An optional's representation is nullish exactly for `none`. -/
theorem option_nullish {n : Nullish} {σ : Ty} {w : JSValue} {x : Option σ.denote} (hσ : σ.nonNullish = true)
    (h : (Ty.option n σ).Rep w x) : w.nullish = x.isNone := by
  cases x with
  | none => exact Nullish.admits_nullish h
  | some y => exact Ty.rep_not_nullish hσ h

theorem looseEq_null {w : JSValue} : binary .looseEq w (Lit.value .null) = .ok (.bool w.nullish) := by
  cases w <;> rfl

theorem looseNe_null {w : JSValue} : binary .looseNe w (Lit.value .null) = .ok (.bool !w.nullish) := by
  cases w <;> rfl

theorem conv_args1 {prog : Program} {env : Env} {e : Expr} {v : JSValue}
    (h : Converges (fun n => evalExpr prog n env e) (.ok v)) :
    Converges (fun n => evalArgs prog n env [e]) (.ok [v]) := by
  obtain ⟨N, h⟩ := h
  refine Converges.of_succ (N + 1) fun m hm => ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [evalArgs, h (k + 1) (by omega), bind, Except.bind, pure, Except.pure]

section
variable {prog : Program} {Φ : Sigs} {fs : Φ.denote} {ss : Φ.safety} (hfs : FnsOK prog fs ss)
include hfs

/-- `x == null` on a variable holding an optional. -/
theorem nullTest_converges {Γ : Ctx} {x : String} {n : Nullish} {σ : Ty} (v : Var Γ x (.option n σ))
    (hσ : σ.nonNullish = true) {env : Env} {ρ : Γ.denote} (he : EnvRel Γ env ρ) :
    Converges (fun m => evalExpr prog m env (nullTest x)) (.ok (.bool (v.get ρ).isNone)) := by
  obtain ⟨w, hl, hw⟩ := v.lookup he
  refine Converges.of_succ 1 fun m hm => ?_
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hn : JSValue.null.nullish = true := rfl
  simp [nullTest, evalExpr, hl, bind, Except.bind, binary, Lit.value, option_nullish hσ hw, hn]

theorem notNullTest_converges {Γ : Ctx} {x : String} {n : Nullish} {σ : Ty} (v : Var Γ x (.option n σ))
    (hσ : σ.nonNullish = true) {env : Env} {ρ : Γ.denote} (he : EnvRel Γ env ρ) :
    Converges (fun m => evalExpr prog m env (notNullTest x)) (.ok (.bool (v.get ρ).isSome)) := by
  obtain ⟨w, hl, hw⟩ := v.lookup he
  refine Converges.of_succ 1 fun m hm => ?_
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := option_nullish hσ hw
  cases h : v.get ρ <;> simp_all [notNullTest, evalExpr, hl, bind, Except.bind, binary, Lit.value, JSValue.nullish]

/-- Narrowing an optional variable known to hold `some y`. -/
theorem narrow_some {Γ : Ctx} {x : String} {n : Nullish} {σ : Ty} (v : Var Γ x (.option n σ)) {env : Env}
    {ρ : Γ.denote} {y : σ.denote} (he : EnvRel Γ env ρ) (hy : v.get ρ = some y) :
    EnvRel (v.narrow σ) env (v.narrowVal ρ y) :=
  v.narrowRel he fun w _ hw => by rw [hy] at hw; exact hw

variable (hss : SafeSigs ss)
include hss

mutual
  theorem TExpr.adequate : ∀ {Γ : Ctx} {τ : Ty} (e : TExpr Φ Γ τ) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      e.safe fs ss ρ = true →
      ∃ w, Converges (fun n => evalExpr prog n env e.erase) (.ok w) ∧ τ.Rep w (e.denote fs ρ)
    | _, _, .bool b, _, _, _, _ =>
      ⟨.bool b, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], rfl⟩
    | _, _, .int b, _, _, _, _ =>
      ⟨.bigint b, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], rfl⟩
    | _, _, .str b, _, _, _, _ =>
      ⟨.string b, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], rfl⟩
    | _, _, .tagLit t, _, _, _, _ =>
      ⟨t.value, Converges.of_succ 0 fun m _ => by cases t <;> simp [evalExpr, TExpr.erase, TagLit.lit, TagLit.value,
        Lit.value], rfl⟩
    | _, _, .litIn a as i, _, _, _, _ =>
      ⟨.string ((a :: as)[i]), Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], rfl⟩
    | _, _, .undef _ _ h, _, _, _, _ =>
      ⟨.undefined, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], Nullish.admits_undef h⟩
    | _, _, .null _ _ h, _, _, _, _ =>
      ⟨.null, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], Nullish.admits_null h⟩
    | _, _, .var v, _, _, he, _ => by
      obtain ⟨w, hl, hw⟩ := v.lookup he
      exact ⟨w, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, hl], hw⟩
    | _, _, .widen N e, _, _, he, hs => by
      obtain ⟨w, hc, hw⟩ := TExpr.adequate e he hs
      exact ⟨w, hc, N.rep hw⟩
    | _, _, .not e, _, ρ, he, hs => by
      obtain ⟨w, ⟨N, hc⟩, hw⟩ := TExpr.adequate e he hs
      simp only [Ty.Rep] at hw; subst hw
      exact ⟨.bool (!e.denote fs ρ), Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, unary], rfl⟩
    | _, _, .neg e, _, ρ, he, hs => by
      obtain ⟨w, ⟨N, hc⟩, hw⟩ := TExpr.adequate e he hs
      simp only [Ty.Rep] at hw; subst hw
      exact ⟨.bigint (-e.denote fs ρ), Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, unary], rfl⟩
    | _, _, .bin op a b, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hab := andT_elim (op.guard_elim hs) (a.safe_of_trivial ρ) (b.safe_of_trivial ρ)
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hab.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hab.2
      obtain ⟨w, hw, hr⟩ := op.sound hwa hwb hs
      exact ⟨w, converges_binary (by cases op <;> simp [Op.js]) ha hb hw, hr⟩
    | _, _, .and a b, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => by split <;> simp [b.safe_of_trivial ρ h])
      obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he hs.1
      simp only [Ty.Rep] at hwa; subst hwa
      cases hx : a.denote fs ρ
      · exact ⟨.bool false, Converges.of_succ Na fun m hm => by
          simp [evalExpr, TExpr.erase, ha m hm, hx, bind, Except.bind], by simp [TExpr.denote, hx, Ty.Rep]⟩
      · obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (by simpa [hx] using hs.2)
        exact ⟨wb, Converges.of_succ (max Na Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
    | _, _, .or a b, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => by split <;> simp [b.safe_of_trivial ρ h])
      obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he hs.1
      simp only [Ty.Rep] at hwa; subst hwa
      cases hx : a.denote fs ρ
      · obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (by simpa [hx] using hs.2)
        exact ⟨wb, Converges.of_succ (max Na Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      · exact ⟨.bool true, Converges.of_succ Na fun m hm => by
          simp [evalExpr, TExpr.erase, ha m hm, hx, bind, Except.bind], by simp [TExpr.denote, hx, Ty.Rep]⟩
    | _, _, .cond c a b, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (c.safe_of_trivial ρ) (fun h => by
        simp only [Bool.and_eq_true] at h; split <;> simp [h.1, h.2])
      obtain ⟨wc, ⟨Nc, hc⟩, hwc⟩ := TExpr.adequate c he hs.1
      simp only [Ty.Rep] at hwc; subst hwc
      cases hx : c.denote fs ρ
      · obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (TExpr.ok (by simpa [hx] using hs.2))
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      · obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he (TExpr.ok (by simpa [hx] using hs.2))
        exact ⟨wa, Converges.of_succ (max Nc Na) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), ha m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwa⟩
    | _, _, .isNull hσ e, _, ρ, he, hs => by
      obtain ⟨w, ha, hw⟩ := TExpr.adequate e he hs
      exact ⟨.bool w.nullish, converges_binary (by simp) ha (Converges.of_succ 0 fun m _ => by simp [evalExpr])
        looseEq_null, by simp [Ty.Rep, TExpr.denote, option_nullish hσ hw]⟩
    | _, _, .notNull hσ e, _, ρ, he, hs => by
      obtain ⟨w, ha, hw⟩ := TExpr.adequate e he hs
      exact ⟨.bool !w.nullish, converges_binary (by simp) ha (Converges.of_succ 0 fun m _ => by simp [evalExpr])
        looseNe_null, by simp [Ty.Rep, TExpr.denote, option_nullish hσ hw]⟩
    | _, _, .condNull v hσ a b, _, ρ, he, hs => by
      obtain ⟨Nc, hc⟩ := nullTest_converges hfs v hσ he
      cases hx : v.get ρ with
      | none =>
        obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he (TExpr.ok (by simpa [TExpr.safe, hx] using hs))
        exact ⟨wa, Converges.of_succ (max Nc Na) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), ha m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwa⟩
      | some y =>
        obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b (narrow_some hfs v he hx) (TExpr.ok (by simpa [TExpr.safe, hx] using hs))
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
    | _, _, .condNotNull v hσ a b, _, ρ, he, hs => by
      obtain ⟨Nc, hc⟩ := notNullTest_converges hfs v hσ he
      cases hx : v.get ρ with
      | none =>
        obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (TExpr.ok (by simpa [TExpr.safe, hx] using hs))
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      | some y =>
        obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a (narrow_some hfs v he hx) (TExpr.ok (by simpa [TExpr.safe, hx] using hs))
        exact ⟨wa, Converges.of_succ (max Nc Na) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), ha m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwa⟩
    | _, _, .coalesce hσ a b, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => by split <;> simp [b.safe_of_trivial ρ h])
      obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he hs.1
      have hn := option_nullish hσ hwa
      cases hx : a.denote fs ρ with
      | none =>
        obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (by simpa [hx] using hs.2)
        exact ⟨wb, Converges.of_succ (max Na Nb) fun m hm => by
          simp_all [evalExpr, TExpr.erase, ha m (by omega), hb m (by omega), bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      | some y =>
        exact ⟨wa, Converges.of_succ Na fun m hm => by
          simp_all [evalExpr, TExpr.erase, ha m hm, bind, Except.bind],
          by simpa [TExpr.denote, hx, Ty.Rep] using hwa⟩
    | _, _, .call fn hf args, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      simp only [Bool.or_eq_false_iff] at hf
      have hs := andT_elim hs (args.safe_of_trivial ρ) (hss fn _)
      obtain ⟨vs, ⟨Na, ha⟩, hvs⟩ := TArgs.adequate args he hs.1
      obtain ⟨w, ⟨Nc, hc⟩, hw⟩ := hfs.conv fn _ vs hf.2 hvs hs.2
      exact ⟨w, Converges.of_succ (max Na Nc) fun m hm => by
        simp [evalExpr, TExpr.erase, ha m (by omega), hc m (by omega), he.lookup_none hf.1, bind, Except.bind],
        hw⟩
    | _, _, .newMap _, _, _, _, _ =>
      ⟨.map [], Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase], [], rfl, .nil⟩
    | _, _, .stateGet v i hn k, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      obtain ⟨kvs, hsm, hrel⟩ := stateMap_rep v i he
      obtain ⟨wk, ⟨N, hk⟩, hwk⟩ := TExpr.adequate k he hs
      simp only [Ty.Rep] at hwk; subst hwk
      refine ⟨(mapGet kvs (k.denote fs ρ)).getD .undefined, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hsm, hk m hm, mapKey, bind, Except.bind, pure, Except.pure], ?_⟩
      show (Ty.option .undef _).Rep _ (mapGet _ _)
      rcases mapGet_rep (k.denote fs ρ) hrel with ⟨h1, h2⟩ | ⟨w, x, h1, h2, hw⟩
      · rw [h1, h2]; rfl
      · rw [h1, h2]; exact hw
    | _, _, .stateHas v i k, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      obtain ⟨kvs, hsm, hrel⟩ := stateMap_rep v i he
      obtain ⟨wk, ⟨N, hk⟩, hwk⟩ := TExpr.adequate k he hs
      simp only [Ty.Rep] at hwk; subst hwk
      have : (mapGet kvs (k.denote fs ρ)).isSome = (mapGet (i.get (v.get ρ)) (k.denote fs ρ)).isSome := by
        rcases mapGet_rep (k.denote fs ρ) hrel with ⟨h1, h2⟩ | ⟨w, x, h1, h2, _⟩ <;> simp [h1, h2]
      exact ⟨.bool (mapGet kvs (k.denote fs ρ)).isSome, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hsm, hk m hm, mapKey, bind, Except.bind, pure, Except.pure], by
        simp only [Ty.Rep, TExpr.denote, this]⟩
    | _, _, .stateSize v i, env, ρ, he, _ => by
      obtain ⟨kvs, hsm, hrel⟩ := stateMap_rep v i he
      exact ⟨.number kvs.length, Converges.of_succ 0 fun m _ => by
        simp [evalExpr, TExpr.erase, hsm, bind, Except.bind, pure, Except.pure], by
        simp only [Ty.Rep, TExpr.denote, hrel.length_eq]⟩
    | _, _, @TExpr.callThis _ _ _ m _ _ _ _ fn v args, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (args.safe_of_trivial ρ) (hss fn _)
      obtain ⟨vs, ⟨Na, ha⟩, hvs⟩ := TArgs.adequate args he hs.1
      obtain ⟨t, ht, hwt⟩ := thisOf_rep v he
      obtain ⟨w, ⟨Nc, hc⟩, hw⟩ := hfs.conv fn (v.get ρ, args.denote fs ρ) (t :: vs) rfl
        ⟨t, _, rfl, hwt, hvs⟩ hs.2
      exact ⟨w, Converges.of_succ (max Na Nc) fun n hn => by
        simp [evalExpr, TExpr.erase, ha n (by omega), ht, hc n (by omega), bind, Except.bind, pure, Except.pure],
        hw⟩
    | _, _, .record es sel hl, env, ρ, he, hs => by
      obtain ⟨ps, ⟨N, hc⟩, hn, hr⟩ := TEntries.adequate es [] hl he hs
      have hd : (ps.map Prod.fst).Nodup := by rw [hn]; exact Fields.literalNames_nodup hl
      exact ⟨.record ps, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, upsertAll_nil _ hd], ps, rfl, hd, sel.rep hn hr⟩
    | _, _, .update r es u hl, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (r.safe_of_trivial ρ) (es.safe_of_trivial ρ)
      obtain ⟨wr, ⟨Nr, hcr⟩, rkvs, rfl, hrd, hrr⟩ := TExpr.adequate r he hs.1
      obtain ⟨ps, ⟨N, hc⟩, hn, hrep⟩ := TEntries.adequate es rkvs hl he hs.2
      have hd : (ps.map Prod.fst).Nodup := by rw [hn]; exact Fields.literalNames_nodup hl
      refine ⟨.record (upsertAll rkvs ps), Converges.of_succ (max Nr N + 1) fun m hm => ?_, _, rfl, nodup_upsertAll _ _ hrd,
        u.rep hn hd hrep hrr⟩
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [evalExpr, TExpr.erase, evalEntries, hcr m (by omega), hc m (by omega), spreadInto_record,
        upsertAll_nil _ hrd, bind, Except.bind]
    | _, _, .field e i hp, env, ρ, he, hs => by
      obtain ⟨w, ⟨N, hc⟩, kvs, rfl, _, hr⟩ := TExpr.adequate e he hs
      exact ⟨_, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, getField_record hp], i.rep hr⟩
    | _, _, .num n, _, _, _, _ =>
      ⟨.number n, Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, Lit.value], rfl⟩
    | _, _, .negNum n h, _, _, _, _ =>
      ⟨.number (-n), Converges.of_succ 1 fun m hm => by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have h' : inRange (-n) = true := by simp [inRange, Int.natAbs_neg] at h ⊢; exact h
        simp [evalExpr, TExpr.erase, Lit.value, unary, number_ok h', bind, Except.bind], rfl⟩
    | _, _, .nneg e, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨w, ⟨N, hc⟩, hw⟩ := TExpr.adequate e he (TExpr.ok hs.1)
      simp only [Ty.Rep] at hw; subst hw
      exact ⟨.number (-e.denote fs ρ), Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, unary, number_ok hs.2], rfl⟩
    | _, _, .array es, _, ρ, he, hs => by
      obtain ⟨ws, ⟨N, hc⟩, hws⟩ := TElems.adequate es he hs
      exact ⟨.array ws, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, pure, Except.pure], ws, rfl, hws⟩
    | _, _, .length a, _, ρ, he, hs => by
      obtain ⟨_, ⟨N, hc⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs
      exact ⟨.number vs.length, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, getField], by
        simp [Ty.Rep, TExpr.denote, hvs.length_eq]⟩
    | _, _, .slength e, _, ρ, he, hs => by
      obtain ⟨w, ⟨N, hc⟩, hw⟩ := TExpr.adequate e he hs
      simp only [Ty.Rep] at hw; subst hw
      exact ⟨.number (e.denote fs ρ).length, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, bind, Except.bind, getField], rfl⟩
    | _, _, .index a i, _, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (i.safe_of_trivial ρ)
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨wi, ⟨Ni, hi⟩, hwi⟩ := TExpr.adequate i he hs.2
      simp only [Ty.Rep] at hwi; subst hwi
      exact ⟨if 0 ≤ i.denote fs ρ then (vs[(i.denote fs ρ).toNat]?).getD .undefined else .undefined,
        Converges.of_succ (max Na Ni) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hi m (by omega), bind, Except.bind, index],
        index_rep hvs _⟩
    | _, _, .includes hp a e, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (e.safe_of_trivial ρ)
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨wx, hx, hwx⟩ := TExpr.adequate e he hs.2
      obtain ⟨Nx, hx⟩ := conv_args1 hx
      exact ⟨.bool ((a.denote fs ρ).any fun y => Ty.beq _ y (e.denote fs ρ)),
        Converges.of_succ (max Na Nx) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hx m (by omega), includes_rep hp hwx hvs, bind,
            Except.bind, pure, Except.pure], rfl⟩
    | _, _, .any a p, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => anySafe_true (fun y => p.safe_of_trivial hss ρ y h) _)
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TFn.adequate p he
      obtain ⟨Ns, hr⟩ := someApply_conv (PredOK.of (arr := .array vs) happ) 0 hvs hs.2
      exact ⟨.bool ((a.denote fs ρ).any (p.denote fs ρ)), Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), bind, Except.bind,
            pure, Except.pure], rfl⟩
    | _, _, .all a p, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => allSafe_true (fun y => p.safe_of_trivial hss ρ y h) _)
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TFn.adequate p he
      obtain ⟨Ns, hr⟩ := everyApply_conv (PredOK.of (arr := .array vs) happ) 0 hvs hs.2
      exact ⟨.bool ((a.denote fs ρ).all (p.denote fs ρ)), Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), bind, Except.bind,
            pure, Except.pure], rfl⟩
    | _, _, .find a p, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => anySafe_true (fun y => p.safe_of_trivial hss ρ y h) _)
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TFn.adequate p he
      obtain ⟨r, ⟨Ns, hr⟩, hrep⟩ := findApply_conv (PredOK.of (arr := .array vs) happ) 0 hvs hs.2
      exact ⟨r, Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), bind, Except.bind,
            pure, Except.pure], hrep⟩
    | _, _, .filter a p, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => by simp [p.safe_of_trivial hss ρ _ h])
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TFn.adequate p he
      obtain ⟨rs, ⟨Ns, hr⟩, hrep⟩ := filterApply_conv (PredOK.of (arr := .array vs) happ) 0 hvs hs.2
      exact ⟨.array rs, Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), bind, Except.bind,
            pure, Except.pure], rs, rfl, hrep⟩
    | _, _, .map a p, env, ρ, he, hs => by
      simp only [TExpr.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (fun h => by simp [p.safe_of_trivial hss ρ _ h])
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TFn.adequate p he
      obtain ⟨rs, ⟨Ns, hr⟩, hrep⟩ := mapApply_conv (arr := .array vs) (fun i w y hw hsy => happ _ w y hw hsy) 0 hvs hs.2
      exact ⟨.array rs, Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), bind, Except.bind,
            pure, Except.pure], rs, rfl, hrep⟩
    | _, _, .sorted a c, env, ρ, he, hs => by
      simp only [TExpr.safe, sortSafe, Bool.and_eq_true] at hs
      have hall := orT_elim hs.2.1 (fun h => by simp [c.safe_of_trivial hss ρ _ _ h])
      obtain ⟨_, ⟨Na, ha⟩, vs, rfl, hvs⟩ := TExpr.adequate a he (TExpr.ok hs.1)
      obtain ⟨f, ⟨Nf, hf⟩, happ⟩ := TCmp.adequate c he
      obtain ⟨Ns, hr⟩ := compareAll_conv happ hvs hvs hall
      have hcons := hs.2.2
      simp only [signs] at hcons
      exact ⟨.array ((sortIndices (signs (c.denote fs ρ) (a.denote fs ρ)) vs.length).filterMap (vs[·]?)),
        Converges.of_succ (max Na (max Nf Ns)) fun m hm => by
          simp [evalExpr, TExpr.erase, ha m (by omega), hf m (by omega), hr m (by omega), hcons, signs, bind,
            Except.bind, pure, Except.pure], _, rfl, sortedBy_rep hvs _⟩

  theorem TArgs.adequate : ∀ {Γ ps : Ctx} (args : TArgs Φ Γ ps) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      args.safe fs ss ρ = true →
      ∃ vs, Converges (fun n => evalArgs prog n env args.erase) (.ok vs) ∧ ArgsRep ps vs (args.denote fs ρ)
    | _, _, .nil, _, _, _, _ => ⟨[], Converges.of_succ 0 fun m _ => by simp [evalArgs, TArgs.erase], rfl⟩
    | _, _, .omitted h, _, _, _, _ =>
      ⟨[], Converges.of_succ 0 fun m _ => by simp [evalArgs, TArgs.erase], ArgsRep.omitted h⟩
    | _, _, .cons e rest, _, ρ, he, hs => by
      simp only [TArgs.safe] at hs
      have hs := andT_elim hs (e.safe_of_trivial ρ) (rest.safe_of_trivial ρ)
      obtain ⟨w, ⟨Ne, hce⟩, hw⟩ := TExpr.adequate e he hs.1
      obtain ⟨vs, ⟨Nr, hcr⟩, hvs⟩ := TArgs.adequate rest he hs.2
      exact ⟨w :: vs, Converges.of_succ (max Ne Nr) fun m hm => by
        simp [evalArgs, TArgs.erase, hce m (by omega), hcr m (by omega), bind, Except.bind, pure, Except.pure],
        ⟨w, _, rfl, hw, hvs⟩⟩

  /-- A literal's entries define distinct fields, in order, on top of `kvs0`. -/
  theorem TEntries.adequate : ∀ {Γ : Ctx} {src : Fields} (es : TEntries Φ Γ src) (kvs0 : List (String × JSValue))
      {env : Env} {ρ : Γ.denote}, src.literalNames = true → EnvRel Γ env ρ → es.safe fs ss ρ = true →
      ∃ ps, Converges (fun n => evalEntries prog n env kvs0 es.erase) (.ok (.record (upsertAll kvs0 ps))) ∧
        ps.map Prod.fst = src.names ∧ src.Rep ps (es.denote fs ρ)
    | _, _, .nil, kvs0, _, _, _, _, _ =>
      ⟨[], Converges.of_succ 0 fun m _ => by simp [evalEntries, TEntries.erase, upsertAll], rfl, trivial⟩
    | _, _, .cons f e rest, kvs0, _, ρ, hl, he, hs => by
      simp only [TEntries.safe] at hs
      have hs := andT_elim hs (e.safe_of_trivial ρ) (rest.safe_of_trivial ρ)
      have hl' := Fields.literalNames_cons hl
      obtain ⟨w, ⟨Ne, hce⟩, hw⟩ := TExpr.adequate e he hs.1
      obtain ⟨ps, ⟨Nr, hcr⟩, hn, hr⟩ := TEntries.adequate rest (upsert kvs0 f w) hl'.2.2 he hs.2
      refine ⟨(f, w) :: ps, Converges.of_succ (max Ne Nr) fun m hm => ?_, by simp [hn, Fields.names], ?_⟩
      · simp [evalEntries, TEntries.erase, hce m (by omega), hcr m (by omega), setField, hl'.1, upsertAll,
          bind, Except.bind]
      · refine ⟨by simpa [fieldOf, List.lookup] using hw, Fields.rep_congr (fun g hg => ?_) hr⟩
        have : g ≠ f := fun h => hl'.2.1 (h ▸ hg)
        simp [fieldOf, List.lookup, beq_eq_false_iff_ne.mpr this]

  /-- A callback evaluates to a function value which, applied to an element (and any
  further arguments), converges to its denotation. -/
  theorem TFn.adequate : ∀ {Γ : Ctx} {τ σ : Ty} (p : TFn Φ Γ τ σ) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      ∃ f, Converges (fun n => evalArgs prog n env [p.erase]) (.ok [f]) ∧
        ∀ (extra : List JSValue) w y, τ.Rep w y → p.safe fs ss ρ y = true →
          ∃ r, Converges (fun n => apply prog n f (w :: extra)) (.ok r) ∧ σ.Rep r (p.denote fs ρ y)
    | _, _, _, .arrow x body, env, ρ, he => ⟨_, conv_arrow, fun extra w y hw hs => by
        obtain ⟨r, hc, hr⟩ := TExpr.adequate body (env := (x, w) :: env) (ρ := (y, ρ)) ⟨w, env, rfl, hw, he⟩ hs
        exact ⟨r, apply_closure1 extra hc, hr⟩⟩
    | _, _, _, .const body, env, ρ, he => ⟨_, conv_arrow, fun extra w y _ hs => by
        obtain ⟨r, ⟨N, hc⟩, hr⟩ := TExpr.adequate body he hs
        exact ⟨r, Converges.of_succ N fun m hm => by simp [apply, bindParams, hc m hm], hr⟩⟩
    | _, _, _, @TFn.ref _ _ _ _ f _ _ _ fn h, env, ρ, he =>
      ⟨.function f, conv_args1 (Converges.of_succ 0 fun m _ => by
          simp [evalExpr, TFn.erase, he.lookup_none h, hfs.mem fn]), fun extra w y hw hs => by
        obtain ⟨r, ⟨N, hc⟩, hr⟩ := hfs.conv fn (y, ()) (w :: extra) rfl ⟨w, [], rfl, hw, rfl⟩ hs
        exact ⟨r, Converges.of_succ N fun m hm => by simp [apply, hc m hm], hr⟩⟩

  theorem TCmp.adequate : ∀ {Γ : Ctx} {τ : Ty} (c : TCmp Φ Γ τ) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      ∃ f, Converges (fun n => evalArgs prog n env [c.erase]) (.ok [f]) ∧
        CmpOK prog τ f (c.denote fs ρ) (c.safe fs ss ρ)
    | _, _, .arrow x y body, env, ρ, he => ⟨_, conv_arrow, fun w₁ a₁ w₂ a₂ h₁ h₂ hs => by
        obtain ⟨r, hc, hr⟩ := TExpr.adequate body (env := (x, w₁) :: (y, w₂) :: env) (ρ := (a₁, a₂, ρ))
          ⟨w₁, _, rfl, h₁, w₂, env, rfl, h₂, he⟩ hs
        simp only [Ty.Rep] at hr; subst hr
        exact apply_closure2 hc⟩
    | _, _, @TCmp.ref _ _ _ f _ _ _ _ fn h, env, ρ, he =>
      ⟨.function f, conv_args1 (Converges.of_succ 0 fun m _ => by
          simp [evalExpr, TCmp.erase, he.lookup_none h, hfs.mem fn]), fun w₁ a₁ w₂ a₂ h₁ h₂ hs => by
        obtain ⟨r, ⟨N, hc⟩, hr⟩ := hfs.conv fn (a₁, a₂, ()) [w₁, w₂] rfl ⟨w₁, _, rfl, h₁, w₂, [], rfl, h₂, rfl⟩ hs
        simp only [Ty.Rep] at hr; subst hr
        exact Converges.of_succ N fun m hm => by simp [apply, hc m hm, TCmp.denote]⟩

  theorem TElems.adequate : ∀ {Γ : Ctx} {τ : Ty} (es : TElems Φ Γ τ) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      es.safe fs ss ρ = true →
      ∃ ws, Converges (fun n => evalElems prog n env es.erase) (.ok ws) ∧
        Forall2 (fun w x => τ.Rep w x) ws (es.denote fs ρ)
    | _, _, .nil, _, _, _, _ => ⟨[], Converges.of_succ 0 fun m _ => by simp [evalElems, TElems.erase], .nil⟩
    | _, _, .cons e rest, _, ρ, he, hs => by
      simp only [TElems.safe] at hs
      have hs := andT_elim hs (e.safe_of_trivial ρ) (rest.safe_of_trivial ρ)
      obtain ⟨w, ⟨Ne, hce⟩, hw⟩ := TExpr.adequate e he hs.1
      obtain ⟨ws, ⟨Nr, hcr⟩, hws⟩ := TElems.adequate rest he hs.2
      exact ⟨w :: ws, Converges.of_succ (max Ne Nr) fun m hm => by
        simp [evalElems, TElems.erase, hce m (by omega), hcr m (by omega), bind, Except.bind, pure, Except.pure],
        .cons hw hws⟩
    | _, _, .spread a rest, _, ρ, he, hs => by
      simp only [TElems.safe] at hs
      have hs := andT_elim hs (a.safe_of_trivial ρ) (rest.safe_of_trivial ρ)
      obtain ⟨_, ⟨Ne, hce⟩, vs, rfl, hvs⟩ := TExpr.adequate a he hs.1
      obtain ⟨ws, ⟨Nr, hcr⟩, hws⟩ := TElems.adequate rest he hs.2
      exact ⟨vs ++ ws, Converges.of_succ (max Ne Nr) fun m hm => by
        simp [evalElems, TElems.erase, hce m (by omega), hcr m (by omega), bind, Except.bind, pure, Except.pure],
        hvs.append hws⟩
    | _, _, .spreadKeys v i rest, _, ρ, he, hs => by
      simp only [TElems.safe] at hs
      obtain ⟨kvs, hsm, hrel⟩ := stateMap_rep v i he
      obtain ⟨ws, ⟨N, hcr⟩, hws⟩ := TElems.adequate rest he hs
      exact ⟨_, Converges.of_succ (N + 1) fun n hn => by
        obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simp [evalElems, TElems.erase, evalExpr, hsm, hcr (n + 1) (by omega), bind, Except.bind, pure, Except.pure],
        (keys_rep hrel).append hws⟩
    | _, _, .spreadValues v i rest, _, ρ, he, hs => by
      simp only [TElems.safe] at hs
      obtain ⟨kvs, hsm, hrel⟩ := stateMap_rep v i he
      obtain ⟨ws, ⟨N, hcr⟩, hws⟩ := TElems.adequate rest he hs
      exact ⟨_, Converges.of_succ (N + 1) fun n hn => by
        obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simp [evalElems, TElems.erase, evalExpr, hsm, hcr (n + 1) (by omega), bind, Except.bind, pure, Except.pure],
        (values_rep hrel).append hws⟩
end

end

end V2

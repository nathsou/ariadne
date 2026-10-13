import V2.Proof.Basic

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
def FnsOK {Φ : Sigs} (prog : Program) (fs : Φ.denote) (ss : Φ.safety) : Prop :=
  ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote) (vs : List JSValue), ArgsRep s.params vs xs →
    v.safe ss xs = true → ∃ w, Converges (fun n => call prog n f vs) (.ok w) ∧ s.result.Rep w (v.get fs xs)

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

theorem Sel.rep : ∀ {fs : Fields} (sel : Sel src fs) {kvs} {xs : src.denote}, src.Rep kvs xs →
    fs.Rep kvs (sel.pick xs)
  | .nil, .nil, _, _, _ => trivial
  | .cons _ _ _, .cons i rest, _, _, h => ⟨i.rep h, rest.rep h⟩

theorem Upd.rep : ∀ {fs : Fields} (u : Upd src fs) {ps rkvs} {xs : src.denote} {r : fs.denote},
    (ps.map Prod.fst) = src.names → (ps.map Prod.fst).Nodup → src.Rep ps xs → fs.Rep rkvs r →
    fs.Rep (upsertAll rkvs ps) (u.apply xs r)
  | .nil, .nil, _, _, _, _, _, _, _, _ => trivial
  | .cons f _ _, .set i rest, ps, rkvs, xs, (_, r), hn, hd, hs, ⟨_, hr⟩ => by
    refine ⟨?_, rest.rep hn hd hs hr⟩
    have hf : f ∈ ps.map Prod.fst := by rw [hn]; exact i.mem
    rw [fieldOf_upsertAll _ _ _ hd, if_pos hf]
    exact i.rep hs
  | .cons f _ _, .keep h rest, ps, rkvs, xs, (_, r), hn, hd, hs, ⟨ha, hr⟩ => by
    refine ⟨?_, rest.rep hn hd hs hr⟩
    have hf : f ∉ ps.map Prod.fst := by rw [hn]; simpa using h
    rw [fieldOf_upsertAll _ _ _ hd, if_neg hf]
    exact ha

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

theorem Nullish.admits_undef {n : Nullish} (h : n.undef? = true) : n.admits .undefined := by
  cases n <;> simp_all [Nullish.undef?, Nullish.admits]

theorem Nullish.admits_null {n : Nullish} (h : n.null? = true) : n.admits .null := by
  cases n <;> simp_all [Nullish.null?, Nullish.admits]

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
    | _, _, .add a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bigint (a.denote fs ρ + b.denote fs ρ), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .sub a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bigint (a.denote fs ρ - b.denote fs ρ), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .mul a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bigint (a.denote fs ρ * b.denote fs ρ), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .lt a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (decide (a.denote fs ρ < b.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .le a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (decide (a.denote fs ρ ≤ b.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .gt a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (decide (b.denote fs ρ < a.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .ge a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (decide (b.denote fs ρ ≤ a.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .concat a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.string (a.denote fs ρ ++ b.denote fs ρ), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .slt a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (strLt (a.denote fs ρ) (b.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .sle a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (strLe (a.denote fs ρ) (b.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .sgt a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (strLt (b.denote fs ρ) (a.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .sge a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      simp only [Ty.Rep] at hwa hwb; subst hwa; subst hwb
      exact ⟨.bool (strLe (b.denote fs ρ) (a.denote fs ρ)), converges_binary (by simp) ha hb rfl, rfl⟩
    | _, _, .eq hp a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      exact ⟨.bool (Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)), converges_binary (by simp) ha hb
        (by simp [binary, Ty.strictEq_rep hp hwa hwb, bind, Except.bind, pure, Except.pure]), rfl⟩
    | _, _, .ne hp a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wa, ha, hwa⟩ := TExpr.adequate a he hs.1
      obtain ⟨wb, hb, hwb⟩ := TExpr.adequate b he hs.2
      exact ⟨.bool (!Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)), converges_binary (by simp) ha hb
        (by simp [binary, Ty.strictEq_rep hp hwa hwb, bind, Except.bind, pure, Except.pure]), rfl⟩
    | _, _, .and a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
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
      simp only [TExpr.safe, Bool.and_eq_true] at hs
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
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨wc, ⟨Nc, hc⟩, hwc⟩ := TExpr.adequate c he hs.1
      simp only [Ty.Rep] at hwc; subst hwc
      cases hx : c.denote fs ρ
      · obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (by simpa [hx] using hs.2)
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      · obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he (by simpa [hx] using hs.2)
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
        obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a he (by simpa [TExpr.safe, hx] using hs)
        exact ⟨wa, Converges.of_succ (max Nc Na) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), ha m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwa⟩
      | some y =>
        obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b (narrow_some hfs v he hx) (by simpa [TExpr.safe, hx] using hs)
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
    | _, _, .condNotNull v hσ a b, _, ρ, he, hs => by
      obtain ⟨Nc, hc⟩ := notNullTest_converges hfs v hσ he
      cases hx : v.get ρ with
      | none =>
        obtain ⟨wb, ⟨Nb, hb⟩, hwb⟩ := TExpr.adequate b he (by simpa [TExpr.safe, hx] using hs)
        exact ⟨wb, Converges.of_succ (max Nc Nb) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), hb m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwb⟩
      | some y =>
        obtain ⟨wa, ⟨Na, ha⟩, hwa⟩ := TExpr.adequate a (narrow_some hfs v he hx) (by simpa [TExpr.safe, hx] using hs)
        exact ⟨wa, Converges.of_succ (max Nc Na) fun m hm => by
          simp [evalExpr, TExpr.erase, hc m (by omega), ha m (by omega), hx, bind, Except.bind],
          by simpa [TExpr.denote, hx] using hwa⟩
    | _, _, .coalesce hσ a b, _, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
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
      simp only [TExpr.safe, Bool.and_eq_true] at hs
      obtain ⟨vs, ⟨Na, ha⟩, hvs⟩ := TArgs.adequate args he hs.1
      obtain ⟨w, ⟨Nc, hc⟩, hw⟩ := hfs fn _ vs hvs hs.2
      exact ⟨w, Converges.of_succ (max Na Nc) fun m hm => by
        simp [evalExpr, TExpr.erase, ha m (by omega), hc m (by omega), he.lookup_none hf, bind, Except.bind],
        hw⟩
    | _, _, .record es sel hl, env, ρ, he, hs => by
      obtain ⟨ps, ⟨N, hc⟩, hn, hr⟩ := TEntries.adequate es [] hl he hs
      have hd : (ps.map Prod.fst).Nodup := by rw [hn]; exact Fields.literalNames_nodup hl
      exact ⟨.record ps, Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, hc m hm, upsertAll_nil _ hd], ps, rfl, hd, sel.rep hr⟩
    | _, _, .update r es u hl, env, ρ, he, hs => by
      simp only [TExpr.safe, Bool.and_eq_true] at hs
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

  theorem TArgs.adequate : ∀ {Γ ps : Ctx} (args : TArgs Φ Γ ps) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
      args.safe fs ss ρ = true →
      ∃ vs, Converges (fun n => evalArgs prog n env args.erase) (.ok vs) ∧ ArgsRep ps vs (args.denote fs ρ)
    | _, _, .nil, _, _, _, _ => ⟨[], Converges.of_succ 0 fun m _ => by simp [evalArgs, TArgs.erase], rfl⟩
    | _, _, .omitted h, _, _, _, _ =>
      ⟨[], Converges.of_succ 0 fun m _ => by simp [evalArgs, TArgs.erase], ArgsRep.omitted h⟩
    | _, _, .cons e rest, _, _, he, hs => by
      simp only [TArgs.safe, Bool.and_eq_true] at hs
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
    | _, _, .cons f e rest, kvs0, _, _, hl, he, hs => by
      simp only [TEntries.safe, Bool.and_eq_true] at hs
      have hl' := Fields.literalNames_cons hl
      obtain ⟨w, ⟨Ne, hce⟩, hw⟩ := TExpr.adequate e he hs.1
      obtain ⟨ps, ⟨Nr, hcr⟩, hn, hr⟩ := TEntries.adequate rest (upsert kvs0 f w) hl'.2.2 he hs.2
      refine ⟨(f, w) :: ps, Converges.of_succ (max Ne Nr) fun m hm => ?_, by simp [hn, Fields.names], ?_⟩
      · simp [evalEntries, TEntries.erase, hce m (by omega), hcr m (by omega), setField, hl'.1, upsertAll,
          bind, Except.bind]
      · refine ⟨by simpa [fieldOf, List.lookup] using hw, Fields.rep_congr (fun g hg => ?_) hr⟩
        have : g ≠ f := fun h => hl'.2.1 (h ▸ hg)
        simp [fieldOf, List.lookup, beq_eq_false_iff_ne.mpr this]
end

end

end V2

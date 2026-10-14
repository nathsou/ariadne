import V2.Typed.Denote

/-!
# Foundations of the adequacy proof

The environment relation, and facts about representation, narrowing and records
that the proof by induction on typed syntax uses.
-/

set_option linter.unusedSimpArgs false

namespace V2

/-! ## Fuel -/

/-- A run converges once every budget from some point on gives the result. -/
theorem Converges.of_succ {f : Nat → α} {a : α} (N : Nat) (h : ∀ m, N ≤ m → f (m + 1) = a) :
    Converges f a :=
  ⟨N + 1, fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact h k (by omega)⟩

/-! ## Environments -/

/-- The environment holds, position by position, the context's names bound to
values representing `ρ`'s components. -/
def EnvRel : (Γ : Ctx) → Env → Γ.denote → Prop
  | [], env, _ => env = []
  | (x, τ) :: Γ, env, (a, ρ) => ∃ w env', env = (x, w) :: env' ∧ τ.Rep w a ∧ EnvRel Γ env' ρ

theorem EnvRel.length : ∀ {Γ : Ctx} {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ → env.length = Γ.length
  | [], _, _, h => by simp [EnvRel] at h; simp [h]
  | (_, _) :: _, _, (_, _), ⟨_, _, rfl, _, h⟩ => by simp [h.length]

theorem Var.lookup : ∀ {Γ : Ctx} {x τ} (v : Var Γ x τ) {env : Env} {ρ : Γ.denote}, EnvRel Γ env ρ →
    ∃ w, env.lookup x = some w ∧ τ.Rep w (v.get ρ)
  | _ :: _, _, _, .here, _, (_, _), ⟨w, _, rfl, hw, _⟩ => ⟨w, by simp, hw⟩
  | _ :: _, _, _, .there h v, _, (_, _), ⟨_, _, rfl, _, rest⟩ => by
    obtain ⟨w, hl, hw⟩ := v.lookup rest
    exact ⟨w, by simp [List.lookup, beq_eq_false_iff_ne.mpr h, hl], hw⟩

/-- Narrowing keeps the environment: the variable's value represents the narrowed
value too. -/
theorem Var.narrowRel : ∀ {Γ : Ctx} {x τ σ} (v : Var Γ x τ) {env : Env} {ρ : Γ.denote} {y : σ.denote},
    EnvRel Γ env ρ → (∀ w, env.lookup x = some w → τ.Rep w (v.get ρ) → σ.Rep w y) →
    EnvRel (v.narrow σ) env (v.narrowVal ρ y)
  | _ :: _, _, _, _, .here, _, (_, _), _, ⟨w, env', rfl, hw, rest⟩, h => ⟨w, env', rfl, h w (by simp) hw, rest⟩
  | _ :: _, _, _, _, .there hne v, _, (_, _), _, ⟨w, env', rfl, hw, rest⟩, h =>
    ⟨w, env', rfl, hw, v.narrowRel rest fun w' hl hw' =>
      h w' (by simp [List.lookup, beq_eq_false_iff_ne.mpr hne, hl]) hw'⟩

theorem Var.widenRel : ∀ {Γ : Ctx} {x τ σ} (v : Var Γ x τ) (e : σ.denote → τ.denote) {env : Env}
    {ρ : (v.narrow σ).denote}, (∀ w y, σ.Rep w y → τ.Rep w (e y)) →
    EnvRel (v.narrow σ) env ρ → EnvRel Γ env (v.widen e ρ)
  | (_, _) :: _, _, _, _, .here, _, _, _, he, h => by
    obtain ⟨w, env', rfl, hw, rest⟩ := h
    exact ⟨w, env', rfl, he w _ hw, rest⟩
  | (_, _) :: _, _, _, _, .there _ v, _, _, _, he, h => by
    obtain ⟨w, env', rfl, hw, rest⟩ := h
    exact ⟨w, env', rfl, hw, v.widenRel _ he rest⟩

/-- Assignment updates the variable's binding in place. -/
theorem Var.assignRel : ∀ {Γ : Ctx} {x τ} (v : Var Γ x τ) {env : Env} {ρ : Γ.denote} {w : JSValue} {a : τ.denote},
    EnvRel Γ env ρ → τ.Rep w a → ∃ env', assign x w env = .ok env' ∧ env'.length = env.length ∧ EnvRel Γ env' (v.set ρ a)
  | _ :: _, _, _, .here, _, (_, _), w, _, ⟨_, env', rfl, _, rest⟩, hw =>
    ⟨(_, w) :: env', by simp [assign], rfl, w, env', rfl, hw, rest⟩
  | _ :: _, _, _, .there hne v, _, (_, _), _, _, ⟨w', env', rfl, hw', rest⟩, hw => by
    obtain ⟨env'', ha, hl, hr⟩ := v.assignRel rest hw
    refine ⟨_ :: env'', ?_, by simp [hl], w', env'', rfl, hw', hr⟩
    simp [assign, beq_eq_false_iff_ne.mpr (Ne.symm hne), ha, bind, Except.bind, pure, Except.pure]

/-- Arguments bound to parameters, as a call does. -/
def ArgsRep (ps : Ctx) (vs : List JSValue) (xs : ps.denote) : Prop := EnvRel ps (bindParams (ps.map Prod.fst) vs) xs

/-! ## Representation -/

theorem Ty.rep_not_nullish : ∀ {τ : Ty} {w : JSValue} {x : τ.denote}, τ.nonNullish = true → τ.Rep w x →
    w.nullish = false
  | .bool, _, _, _, h | .int, _, _, _, h | .number, _, _, _, h | .string, _, _, _, h | .lits _ _, _, _, _, h => by
    simp only [Ty.Rep] at h; subst h; rfl
  | .tag t, _, _, _, h => by simp only [Ty.Rep] at h; subst h; cases t <;> rfl
  | .option _ _, _, _, hn, _ => by simp [Ty.nonNullish] at hn
  | .record _, _, _, _, ⟨_, h, _⟩ | .union _ _, _, _, _, ⟨_, h, _⟩ | .array _, _, _, _, ⟨_, h, _⟩
  | .map _, _, _, _, ⟨_, h, _⟩ => by subst h; rfl

theorem Nullish.admits_nullish : ∀ {n : Nullish} {w : JSValue}, n.admits w → w.nullish = true
  | .undef, _, h | .null, _, h => by simp only [Nullish.admits] at h; subst h; rfl
  | .both, _, h => by rcases h with h | h <;> subst h <;> rfl

theorem distinctStrs_getElem : ∀ {l : List JSString}, distinctStrs l = true →
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), l[i] = l[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (by simp)
  | x :: xs, h, i, j, hi, hj, he => by
    simp only [distinctStrs, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hx : x ∉ xs := by simpa using h.1
    match i, j with
    | 0, 0 => rfl
    | 0, j + 1 =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
      exact absurd (he ▸ List.getElem_mem (by simpa using hj)) hx
    | i + 1, 0 =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
      exact absurd (he.symm ▸ List.getElem_mem (by simpa using hi)) hx
    | i + 1, j + 1 =>
      simp only [List.getElem_cons_succ] at he
      simp [distinctStrs_getElem h.2 i j (by simpa using hi) (by simpa using hj) he]

/-- `===` on representations of primitives is `Ty.beq`. -/
theorem Ty.strictEq_rep : ∀ {τ : Ty} {w₁ w₂ : JSValue} {a b : τ.denote}, τ.prim = true → τ.Rep w₁ a → τ.Rep w₂ b →
    strictEq w₁ w₂ = .ok (τ.beq a b)
  | .bool, _, _, _, _, _, h₁, h₂ | .int, _, _, _, _, _, h₁, h₂ | .number, _, _, _, _, _, h₁, h₂
  | .string, _, _, _, _, _, h₁, h₂ => by
    simp only [Ty.Rep] at h₁ h₂; subst h₁; subst h₂; rfl
  | .lits a as, _, _, i, j, hp, h₁, h₂ => by
    simp only [Ty.Rep] at h₁ h₂; subst h₁; subst h₂
    simp only [strictEq, Ty.beq, Except.ok.injEq]
    by_cases hij : i = j
    · subst hij; simp
    · have : (a :: as)[i] ≠ (a :: as)[j] := fun he =>
        hij (Fin.ext (distinctStrs_getElem hp i j i.isLt j.isLt he))
      have h1 : ((a :: as)[i] == (a :: as)[j]) = false := beq_eq_false_iff_ne.mpr this
      have h2 : (i == j) = false := beq_eq_false_iff_ne.mpr hij
      rw [h1, h2]
  | .tag t, _, _, _, _, _, h₁, h₂ => by
    simp only [Ty.Rep] at h₁ h₂; subst h₁; subst h₂; cases t <;> simp [TagLit.value, strictEq, Ty.beq]
  | .option _ _, _, _, _, _, h, _, _ | .record _, _, _, _, _, h, _, _ | .union _ _, _, _, _, _, h, _, _
  | .array _, _, _, _, _, h, _, _ | .map _, _, _, _, _, h, _, _ => by simp [Ty.prim] at h

theorem VIdx.rep : ∀ {vs : Variants} {t fs} (i : VIdx vs t fs) {key kvs} {y : fs.denote},
    fieldOf kvs key = t.value → fs.Rep kvs y → vs.Rep key kvs (i.inj y)
  | .one _ _, _, _, .one, _, _, _, ht, hy => ⟨ht, hy⟩
  | .cons _ _ _, _, _, .head, _, _, _, ht, hy => ⟨ht, hy⟩
  | .cons _ _ _, _, _, .there i, _, _, _, ht, hy => i.rep ht hy

theorem Narrowing.rep : ∀ {σ τ : Ty} (N : Narrowing σ τ) {w : JSValue} {y : σ.denote}, σ.Rep w y →
    τ.Rep w (N.embed y)
  | _, _, .some _ _, _, _, h => h
  | _, _, .variant i, _, ((), _), ⟨kvs, h, nd, ht, hy⟩ => ⟨kvs, h, nd, i.rep ht hy⟩

theorem FIdx.rep : ∀ {fs : Fields} {f τ} (i : FIdx fs f τ) {kvs} {x : fs.denote}, fs.Rep kvs x →
    τ.Rep (fieldOf kvs f) (i.get x)
  | .cons _ _ _, _, _, .here, _, (_, _), ⟨h, _⟩ => h
  | .cons _ _ _, _, _, .there i, _, (_, _), ⟨_, h⟩ => i.rep h

/-- A field read on a record is `fieldOf`. -/
theorem getField_record {kvs : List (String × JSValue)} {f : String} (h : protoNames.contains f = false) :
    getField (.record kvs) f = .ok (fieldOf kvs f) := by
  simp only [getField, fieldOf]
  cases hl : kvs.lookup f <;> simp_all [protoNames]

/-- Field lists that agree on every lookup represent the same records. -/
theorem Fields.rep_congr : ∀ {fs : Fields} {k₁ k₂ : List (String × JSValue)} {x : fs.denote},
    (∀ f ∈ fs.names, fieldOf k₁ f = fieldOf k₂ f) → fs.Rep k₁ x → fs.Rep k₂ x
  | .nil, _, _, _, _, _ => trivial
  | .cons f _ _, _, _, (_, _), h, ⟨hx, hr⟩ =>
    ⟨by rw [← h f (by simp [Fields.names])]; exact hx,
     Fields.rep_congr (fun g hg => h g (by simp [Fields.names, hg])) hr⟩

theorem distinct_iff : ∀ {xs : List String}, distinct xs = true ↔ xs.Nodup
  | [] => by simp [distinct]
  | x :: xs => by simp [distinct, distinct_iff (xs := xs)]

theorem FIdx.mem : ∀ {fs : Fields} {f τ}, FIdx fs f τ → f ∈ fs.names
  | .cons _ _ _, _, _, .here => by simp [Fields.names]
  | .cons _ _ _, _, _, .there i => by simp [Fields.names, i.mem]

theorem Fields.literalNames_cons {f : String} {τ : Ty} {rest : Fields}
    (h : (Fields.cons f τ rest).literalNames = true) :
    (f == "__proto__") = false ∧ f ∉ rest.names ∧ rest.literalNames = true := by
  simp only [Fields.literalNames, Fields.names, Bool.and_eq_true, Bool.not_eq_true', distinct, List.contains_cons,
    Bool.or_eq_false_iff, Bool.not_eq_true] at h
  obtain ⟨⟨hf, hd⟩, hp, hc⟩ := h
  refine ⟨beq_eq_false_iff_ne.mpr fun h => by simp [h] at hp, by simpa using hf, ?_⟩
  simp only [Fields.literalNames, hd, hc, Bool.not_false, Bool.and_self]

theorem Fields.literalNames_nodup {fs : Fields} (h : fs.literalNames = true) : fs.names.Nodup := by
  simp only [Fields.literalNames, Bool.and_eq_true] at h
  exact distinct_iff.mp h.1

/-! ## Building records -/

theorem lookup_eq_none_of_not_mem {kvs : List (String × JSValue)} {f : String} (h : f ∉ kvs.map Prod.fst) :
    kvs.lookup f = none := by
  induction kvs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map, List.mem_cons, not_or] at h
    have : (f == k) = false := beq_eq_false_iff_ne.mpr h.1
    simp [List.lookup, this, ih h.2]

theorem lookup_upsert (kvs : List (String × JSValue)) (f g : String) (v : JSValue) :
    (upsert kvs f v).lookup g = if g = f then some v else kvs.lookup g := by
  induction kvs with
  | nil => by_cases hg : g = f <;> simp [upsert, List.lookup, hg, beq_eq_false_iff_ne.mpr]
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = f
    · subst hk
      by_cases hg : g = k
      · subst hg; simp [upsert, List.lookup]
      · simp [upsert, List.lookup, beq_eq_false_iff_ne.mpr hg, hg]
    · have hkf : (k == f) = false := beq_eq_false_iff_ne.mpr hk
      by_cases hg : g = k
      · subst hg; simp [upsert, hkf, List.lookup, hk]
      · simp only [upsert, hkf, Bool.false_eq_true, ↓reduceIte, List.lookup, beq_eq_false_iff_ne.mpr hg, ih]

theorem fieldOf_upsert (kvs : List (String × JSValue)) (f g : String) (v : JSValue) :
    fieldOf (upsert kvs f v) g = if g = f then v else fieldOf kvs g := by
  unfold fieldOf; rw [lookup_upsert]; by_cases hg : g = f <;> simp [hg]

theorem keys_upsert (kvs : List (String × JSValue)) (f : String) (v : JSValue) :
    (upsert kvs f v).map Prod.fst = if f ∈ kvs.map Prod.fst then kvs.map Prod.fst else kvs.map Prod.fst ++ [f] := by
  induction kvs with
  | nil => simp [upsert]
  | cons p rest ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = f
    · subst hk; simp [upsert]
    · have hkf : (k == f) = false := beq_eq_false_iff_ne.mpr hk
      simp only [upsert, hkf, Bool.false_eq_true, ↓reduceIte, List.map, ih, List.mem_cons]
      by_cases hm : f ∈ rest.map Prod.fst <;> simp [hm, Ne.symm hk]

theorem nodup_upsert (kvs : List (String × JSValue)) (f : String) (v : JSValue) (h : (kvs.map Prod.fst).Nodup) :
    ((upsert kvs f v).map Prod.fst).Nodup := by
  rw [keys_upsert]
  split
  · exact h
  · next hn =>
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hn ha

/-- The fields an object literal defines, in order, from the empty object. -/
def upsertAll (kvs : List (String × JSValue)) : List (String × JSValue) → List (String × JSValue)
  | [] => kvs
  | (f, v) :: rest => upsertAll (upsert kvs f v) rest

theorem nodup_upsertAll : ∀ (kvs ps : List (String × JSValue)), (kvs.map Prod.fst).Nodup →
    ((upsertAll kvs ps).map Prod.fst).Nodup
  | _, [], h => h
  | _, (_, _) :: rest, h => nodup_upsertAll _ rest (nodup_upsert _ _ _ h)

/-- With distinct new keys, a lookup after defining them finds the new value, or
the old one. -/
theorem fieldOf_upsertAll : ∀ (kvs ps : List (String × JSValue)) (g : String), (ps.map Prod.fst).Nodup →
    fieldOf (upsertAll kvs ps) g = if g ∈ ps.map Prod.fst then fieldOf ps g else fieldOf kvs g
  | kvs, [], g, _ => by simp [upsertAll]
  | kvs, (f, v) :: rest, g, h => by
    simp only [List.map, List.nodup_cons] at h
    rw [upsertAll, fieldOf_upsertAll _ rest g h.2, fieldOf_upsert]
    by_cases hg : g = f
    · subst hg
      have hr : g ∉ rest.map Prod.fst := h.1
      simp [hr, fieldOf, List.lookup]
    · have hb : (g == f) = false := beq_eq_false_iff_ne.mpr hg
      by_cases hr : g ∈ rest.map Prod.fst
      · simp [hr, fieldOf, List.lookup, hb]
      · simp [hr, hg, fieldOf, List.lookup, hb]

theorem spreadInto_record (kvs src : List (String × JSValue)) :
    spreadInto kvs (.record src) = .ok (upsertAll kvs src) := by
  simp only [spreadInto]
  congr 1
  induction src generalizing kvs with
  | nil => rfl
  | cons p rest ih => obtain ⟨f, v⟩ := p; simp [List.foldl, upsertAll, ih]

theorem upsertAll_fresh : ∀ (pre src : List (String × JSValue)), ((pre ++ src).map Prod.fst).Nodup →
    upsertAll pre src = pre ++ src
  | pre, [], _ => by simp [upsertAll]
  | pre, (f, v) :: rest, hn => by
    have hf : f ∉ pre.map Prod.fst := by
      intro hm
      rw [List.map_append, List.nodup_append] at hn
      exact hn.2.2 f hm f (by simp) rfl
    have : upsert pre f v = pre ++ [(f, v)] := by
      clear hn
      induction pre with
      | nil => rfl
      | cons p rest ih =>
        obtain ⟨k, w⟩ := p
        simp only [List.map, List.mem_cons, not_or] at hf
        have hkf : (k == f) = false := beq_eq_false_iff_ne.mpr (Ne.symm hf.1)
        simp [upsert, hkf, ih hf.2]
    rw [upsertAll, this, upsertAll_fresh (pre ++ [(f, v)]) rest (by simpa using hn)]
    simp

/-- Defining a record's own (distinct) fields into the empty object copies it. -/
theorem upsertAll_nil (src : List (String × JSValue)) (h : (src.map Prod.fst).Nodup) : upsertAll [] src = src := by
  simpa using upsertAll_fresh [] src (by simpa using h)

end V2

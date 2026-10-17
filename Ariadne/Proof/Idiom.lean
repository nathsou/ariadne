import Ariadne.Typed.Idiom
import Ariadne.Proof.Direct

/-!
# The denotation with states is the denotation

`TStmts.denoteFn_eq_R`: for every function body, `denoteRFn` (loops and branches threading only the
variables they assign) is `denoteDFn`, and so `denoteFn`.

The proof rests on a frame property: a statement leaves the variables it does not assign alone. Stated
about continuations (`TStmts.denoteD_frame`): two continuations that agree on every environment that agrees
with the current one outside the statement's `writes` give the same result. Then a state holds all a loop
or branch changes: `Ctx.merge m ρ (Ctx.proj m ρ') = ρ'` whenever `ρ'` agrees with `ρ` outside `m`.
-/

set_option linter.unusedSectionVars false

namespace Ariadne

/-! ## Masks -/

def Mask.incl (a b : Mask) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem Mask.getD_or : ∀ (a b : Mask) (i : Nat), (Mask.or a b).getD i false = (a.getD i false || b.getD i false)
  | [], b, i => by simp [Mask.or]
  | a :: m, [], i => by cases i <;> simp [Mask.or]
  | a :: m, b :: m', 0 => by simp [Mask.or]
  | a :: m, b :: m', i + 1 => by simp only [Mask.or, List.getD_cons_succ]; exact Mask.getD_or m m' i

theorem Mask.headD_eq (m : Mask) : m.headD false = m.getD 0 false := by cases m <;> rfl

theorem Mask.tail_getD (m : Mask) (i : Nat) : m.tail.getD i false = m.getD (i + 1) false := by
  cases m <;> simp

theorem Mask.incl_refl (a : Mask) : Mask.incl a a := fun _ h => h

theorem Mask.incl_trans {a b c : Mask} (h1 : Mask.incl a b) (h2 : Mask.incl b c) : Mask.incl a c := fun i h => h2 i (h1 i h)

theorem Mask.or_incl_left {a b c : Mask} (h : Mask.incl (Mask.or a b) c) : Mask.incl a c :=
  fun i hi => h i (by rw [Mask.getD_or, hi]; rfl)

theorem Mask.or_incl_right {a b c : Mask} (h : Mask.incl (Mask.or a b) c) : Mask.incl b c :=
  fun i hi => h i (by rw [Mask.getD_or, hi, Bool.or_true])

/-- Under a binder: the bound variable may change. -/
theorem Mask.incl_cons {a m : Mask} (h : Mask.incl a.tail m) : Mask.incl a (true :: m) := fun i hi => by
  cases i with
  | zero => rfl
  | succ i => exact h i (by rw [Mask.tail_getD]; exact hi)

theorem Mask.incl_cons₂ {a m : Mask} (h : Mask.incl a.tail.tail m) : Mask.incl a (true :: true :: m) :=
  Mask.incl_cons (Mask.incl_cons h)

theorem Mask.incl_tail {a m : Mask} (h : Mask.incl a m) : Mask.incl a.tail m.tail := fun i hi => by
  rw [Mask.tail_getD] at hi ⊢; exact h _ hi

/-! ## Environments that agree outside a mask -/

/-- `ρ` and `ρ'` hold the same values outside the mask's positions. -/
def Agree : (Γ : Ctx) → Mask → Γ.denote → Γ.denote → Prop
  | [], _, _, _ => True
  | (_, _) :: Γ, m, (a, ρ), (b, ρ') => (m.headD false = true ∨ a = b) ∧ Agree Γ m.tail ρ ρ'

theorem Agree.refl : ∀ (Γ : Ctx) (m : Mask) (ρ : Γ.denote), Agree Γ m ρ ρ
  | [], _, _ => trivial
  | (_, _) :: Γ, m, (_, ρ) => ⟨Or.inr rfl, Agree.refl Γ m.tail ρ⟩

theorem Agree.symm : ∀ {Γ : Ctx} {m : Mask} {ρ ρ' : Γ.denote}, Agree Γ m ρ ρ' → Agree Γ m ρ' ρ
  | [], _, _, _, _ => trivial
  | (_, _) :: _, _, (_, _), (_, _), ⟨h1, h2⟩ => ⟨h1.imp id Eq.symm, Agree.symm h2⟩

theorem Agree.trans : ∀ {Γ : Ctx} {m : Mask} {ρ₁ ρ₂ ρ₃ : Γ.denote}, Agree Γ m ρ₁ ρ₂ → Agree Γ m ρ₂ ρ₃ →
    Agree Γ m ρ₁ ρ₃
  | [], _, _, _, _, _, _ => trivial
  | (_, _) :: _, _, (_, _), (_, _), (_, _), ⟨h1, h2⟩, ⟨h1', h2'⟩ =>
    ⟨by rcases h1 with h | h
        · exact Or.inl h
        · rcases h1' with h' | h'
          · exact Or.inl h'
          · exact Or.inr (h.trans h'),
     Agree.trans h2 h2'⟩

theorem Agree.mono : ∀ {Γ : Ctx} {m m' : Mask} {ρ ρ' : Γ.denote}, Mask.incl m m' → Agree Γ m ρ ρ' → Agree Γ m' ρ ρ'
  | [], _, _, _, _, _, _ => trivial
  | (_, _) :: _, m, m', (_, _), (_, _), hm, ⟨h1, h2⟩ =>
    ⟨h1.imp (fun h => by rw [Mask.headD_eq] at h ⊢; exact hm 0 h) id, Agree.mono (Mask.incl_tail hm) h2⟩

/-- Agreeing outside the empty mask is equality. -/
theorem Agree.eq_of_nil : ∀ {Γ : Ctx} {ρ ρ' : Γ.denote}, Agree Γ [] ρ ρ' → ρ = ρ'
  | [], (), (), _ => rfl
  | (_, _) :: _, (_, _), (_, _), ⟨h1, h2⟩ => by
    rcases h1 with h | h
    · exact absurd h (by decide)
    · rw [h, Agree.eq_of_nil h2]

theorem Agree.cons_iff {x : String} {σ : Ty} {Γ : Ctx} {m : Mask} {a b : σ.denote} {ρ ρ' : Γ.denote} :
    Agree ((x, σ) :: Γ) (true :: m) (a, ρ) (b, ρ') ↔ Agree Γ m ρ ρ' := by
  simp [Agree]

theorem Agree.of_cons {x : String} {σ : Ty} {Γ : Ctx} {m : Mask} {ρ ρ' : Ctx.denote ((x, σ) :: Γ)}
    (h : Agree ((x, σ) :: Γ) (true :: m) ρ ρ') : Agree Γ m ρ.2 ρ'.2 := by
  obtain ⟨a, ρ⟩ := ρ; obtain ⟨b, ρ'⟩ := ρ'; exact Agree.cons_iff.mp h

theorem Agree.of_cons₂ {x i : String} {σ σ' : Ty} {Γ : Ctx} {m : Mask}
    {ρ ρ' : Ctx.denote ((x, σ) :: (i, σ') :: Γ)}
    (h : Agree ((x, σ) :: (i, σ') :: Γ) (true :: true :: m) ρ ρ') : Agree Γ m ρ.2.2 ρ'.2.2 :=
  Agree.of_cons (Agree.of_cons h)

/-- Assigning a variable of the mask. -/
theorem Var.agree_set : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) {m : Mask}, Mask.incl v.mask m →
    ∀ (ρ : Γ.denote) (y : τ.denote), Agree Γ m ρ (v.set ρ y)
  | (_, _) :: Γ, _, _, .here, m, h, (a, ρ), y =>
    ⟨Or.inl (by rw [Mask.headD_eq]; exact h 0 rfl), Agree.refl Γ m.tail ρ⟩
  | (_, _) :: Γ, _, _, .there _ v, m, h, (a, ρ), y =>
    ⟨Or.inr rfl, Var.agree_set v (fun i hi => by rw [Mask.tail_getD]; exact h (i + 1) hi) ρ y⟩

/-- Narrowing and widening back: what agrees with the narrowed environment re-embeds into what agrees with
the original one, when the narrowed value re-embeds as the original. -/
theorem Var.agree_widen : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) {σ : Ty} {m : Mask}
    (e : σ.denote → τ.denote) (ρ : Γ.denote) (y : σ.denote) (ρn : (v.narrow σ).denote),
    Agree (v.narrow σ) m (v.narrowVal ρ y) ρn → e y = v.get ρ → Agree Γ m ρ (v.widen e ρn)
  | (_, _) :: Γ, _, _, .here, _, m, e, (a, ρ), y, ρn, h, he => by
    obtain ⟨b, ρn⟩ := ρn
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1.imp id (fun h => by simp only [Var.get] at he; rw [← he, h]), h2⟩
  | (_, _) :: Γ, _, _, .there _ v, _, m, e, (a, ρ), y, ρn, h, he => by
    obtain ⟨b, ρn⟩ := ρn
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, Var.agree_widen v e ρ y ρn h2 he⟩

/-! ## States -/

theorem Ctx.thead_tcons : ∀ {x : String} {τ : Ty} {Δ : Ctx} (a : τ.denote) (t : Δ.tup),
    Ctx.thead (x := x) (Ctx.tcons a t) = a
  | _, _, [], _, _ => rfl
  | _, _, _ :: _, _, _ => rfl

theorem Ctx.ttail_tcons : ∀ {x : String} {τ : Ty} {Δ : Ctx} (a : τ.denote) (t : Δ.tup),
    Ctx.ttail (x := x) (Ctx.tcons a t) = t
  | _, _, [], _, () => rfl
  | _, _, _ :: _, _, _ => rfl

theorem Ctx.tcons_eta : ∀ {x : String} {τ : Ty} {Δ : Ctx} (t : Ctx.tup ((x, τ) :: Δ)),
    Ctx.tcons (Ctx.thead t) (Ctx.ttail t) = t
  | _, _, [], _ => rfl
  | _, _, _ :: _, (_, _) => rfl

theorem Ctx.proj_merge : ∀ (Γ : Ctx) (m : Mask) (ρ : Γ.denote) (s : (Γ.sub m).tup),
    Ctx.proj Γ m (Ctx.merge Γ m ρ s) = s
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | (_, _) :: Γ, true :: m, (_, ρ), s => by
    simp only [Ctx.proj, Ctx.merge, Ctx.proj_merge Γ m ρ, Ctx.tcons_eta]
  | (_, _) :: Γ, false :: m, (_, ρ), s => by
    simp only [Ctx.proj, Ctx.merge, Ctx.proj_merge Γ m ρ]

theorem Ctx.merge_proj : ∀ (Γ : Ctx) (m : Mask) (ρ ρ' : Γ.denote), Agree Γ m ρ ρ' →
    Ctx.merge Γ m ρ (Ctx.proj Γ m ρ') = ρ'
  | [], _, (), (), _ => rfl
  | _ :: _, [], _, _, h => Agree.eq_of_nil h
  | (_, _) :: Γ, true :: m, (_, ρ), (_, ρ'), ⟨_, h⟩ => by
    simp only [Ctx.proj, Ctx.merge, Ctx.thead_tcons, Ctx.ttail_tcons]
    rw [Ctx.merge_proj Γ m ρ ρ' h]
  | (_, _) :: Γ, false :: m, (_, ρ), (_, ρ'), ⟨h1, h⟩ => by
    simp only [Ctx.proj, Ctx.merge]
    rcases h1 with h1 | h1
    · exact absurd h1 Bool.false_ne_true
    · rw [h1, Ctx.merge_proj Γ m ρ ρ' h]

theorem Ctx.agree_merge : ∀ (Γ : Ctx) (m : Mask) (ρ : Γ.denote) (s : (Γ.sub m).tup),
    Agree Γ m ρ (Ctx.merge Γ m ρ s)
  | [], _, _, _ => trivial
  | _ :: _, [], ρ, _ => Agree.refl _ _ ρ
  | (_, _) :: Γ, true :: m, (_, ρ), _ => ⟨Or.inl rfl, Ctx.agree_merge Γ m ρ _⟩
  | (_, _) :: Γ, false :: m, (_, ρ), _ => ⟨Or.inr rfl, Ctx.agree_merge Γ m ρ _⟩

/-! ## Continuations that agree -/

/-- Two continuations that give the same results on every environment agreeing with `ρ` outside `m`. -/
def KAgree (m : Mask) (ρ : Γ.denote) (k k' : K Γ R) : Prop :=
  ∀ ρ', Agree Γ m ρ ρ' → k.normal ρ' = k'.normal ρ' ∧ k.brk ρ' = k'.brk ρ' ∧ k.cont ρ' = k'.cont ρ'

theorem KAgree.of_agree {m : Mask} {ρ ρ₁ : Γ.denote} {k k' : K Γ R} (h : Agree Γ m ρ ρ₁) (hk : KAgree m ρ k k') :
    KAgree m ρ₁ k k' := fun ρ' h' => hk ρ' (Agree.trans h h')

theorem KAgree.mono {m m' : Mask} {ρ : Γ.denote} {k k' : K Γ R} (hm : Mask.incl m m') (hk : KAgree m' ρ k k') :
    KAgree m ρ k k' := fun ρ' h => hk ρ' (Agree.mono hm h)

theorem VIdx.inj_of_proj : ∀ {vs : Variants} {t : TagLit} {fds : Fields} (i : VIdx vs t fds) (u : vs.denote)
    (y : fds.denote), i.proj u = some y → i.inj y = u
  | _, _, _, .one, _, _, h => by simp only [VIdx.proj, Option.some.injEq] at h; exact h.symm
  | _, _, _, .head, .inl _, _, h => by simp only [VIdx.proj, Option.some.injEq] at h; rw [← h]; rfl
  | _, _, _, .head, .inr _, _, h => by simp [VIdx.proj] at h
  | _, _, _, .there _, .inl _, _, h => by simp [VIdx.proj] at h
  | _, _, _, .there i, .inr w, y, h => by
    simp only [VIdx.proj] at h; simp only [VIdx.inj, VIdx.inj_of_proj i w y h]

/-! ## Loops -/

theorem foldl_agree {α : Type} {Γ : Ctx} {m : Mask} (F : Γ.denote → α → Γ.denote)
    (hF : ∀ ρ' y, Agree Γ m ρ' (F ρ' y)) : ∀ (xs : List α) (ρ' : Γ.denote), Agree Γ m ρ' (xs.foldl F ρ')
  | [], ρ' => Agree.refl _ _ ρ'
  | y :: ys, ρ' => Agree.trans (hF ρ' y) (foldl_agree F hF ys _)

/-- Iterations that agree, on continuations that agree, give loops that agree. -/
theorem forIn_frame {α R : Type} {Γ : Ctx} {m : Mask} {ρ : Γ.denote}
    (step : α → (Γ.denote → R) → (Γ.denote → R) → Γ.denote → R)
    (hs : ∀ y n n' e e' ρ', Agree Γ m ρ ρ' → (∀ ρ'', Agree Γ m ρ ρ'' → n ρ'' = n' ρ'' ∧ e ρ'' = e' ρ'') →
      step y n e ρ' = step y n' e' ρ')
    (E E' : Γ.denote → R) (hE : ∀ ρ', Agree Γ m ρ ρ' → E ρ' = E' ρ') :
    ∀ (xs : List α) (ρ' : Γ.denote), Agree Γ m ρ ρ' → forIn xs step E ρ' = forIn xs step E' ρ'
  | [], ρ', h => hE ρ' h
  | y :: ys, ρ', h => hs y _ _ _ _ ρ' h fun ρ'' h' => ⟨forIn_frame step hs E E' hE ys ρ'' h', hE ρ'' h'⟩

theorem whileIn_frame {R : Type} {Γ : Ctx} {m : Mask} {ρ : Γ.denote} (cond : Γ.denote → Bool)
    (step : (Γ.denote → R) → (Γ.denote → R) → Γ.denote → R)
    (hs : ∀ n n' e e' ρ', Agree Γ m ρ ρ' → (∀ ρ'', Agree Γ m ρ ρ'' → n ρ'' = n' ρ'' ∧ e ρ'' = e' ρ'') →
      step n e ρ' = step n' e' ρ')
    (E E' stuck stuck' : Γ.denote → R) (hE : ∀ ρ', Agree Γ m ρ ρ' → E ρ' = E' ρ')
    (hst : ∀ ρ', Agree Γ m ρ ρ' → stuck ρ' = stuck' ρ') :
    ∀ (n : Nat) (ρ' : Γ.denote), Agree Γ m ρ ρ' → whileIn n cond step E stuck ρ' = whileIn n cond step E' stuck' ρ'
  | 0, ρ', h => hst ρ' h
  | n + 1, ρ', h => by
    rw [whileIn_succ, whileIn_succ]
    split
    · exact hs _ _ _ _ ρ' h fun ρ'' h' => ⟨whileIn_frame cond step hs E E' stuck stuck' hE hst n ρ'' h', hE ρ'' h'⟩
    · exact hE ρ' h

section
variable {Φ : Sigs} {fs : Φ.denote}

/-! ## Every result is a continuation's or a `return`'s -/

/-- `Q` holds of every result the continuations give. -/
def K.Inv (Q : R → Prop) (k : K Γ R) : Prop := ∀ ρ, Q (k.normal ρ) ∧ Q (k.brk ρ) ∧ Q (k.cont ρ)

theorem K.Inv.normal {Γ : Ctx} {R : Type} {Q : R → Prop} {k : K Γ R} {n : Γ.denote → R} (hk : K.Inv Q k) (hn : ∀ ρ, Q (n ρ)) :
    K.Inv Q { k with normal := n } := fun ρ => ⟨hn ρ, (hk ρ).2⟩

theorem K.Inv.map {Γ Γ' : Ctx} {R : Type} {Q : R → Prop} {k : K Γ R} (f : Γ'.denote → Γ.denote) (hk : K.Inv Q k) : K.Inv Q (k.map f) :=
  fun ρ => hk (f ρ)

mutual
  theorem TStmts.denoteD_inv : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {R : Type} (Q : R → Prop)
      (r : τ.denote → R) (k : K Γ R) (ρ : Γ.denote), (∀ v, Q (r v)) → K.Inv Q k → Q (st.denoteD fs r k ρ)
    | _, _, .nil, _, _, _, _, ρ, _, hk => (hk ρ).1
    | _, _, .brk _, _, _, _, _, ρ, _, hk => (hk ρ).2.1
    | _, _, .cont _, _, _, _, _, ρ, _, hk => (hk ρ).2.2
    | _, _, .ret _ _, _, _, _, _, _, hr, _ => hr _
    | _, _, .retVoid _ _, _, _, _, _, _, hr, _ => hr _
    | _, _, .const _ _ rest, _, Q, r, _, _, hr, hk => TStmts.denoteD_inv rest Q r _ _ hr (K.Inv.map _ hk)
    | _, _, .let_ _ _ rest, _, Q, r, _, _, hr, hk => TStmts.denoteD_inv rest Q r _ _ hr (K.Inv.map _ hk)
    | _, _, .assign _ _ rest, _, Q, r, k, _, hr, hk => TStmts.denoteD_inv rest Q r k _ hr hk
    | _, _, .stateSet _ _ _ _ _ rest, _, Q, r, k, _, hr, hk => TStmts.denoteD_inv rest Q r k _ hr hk
    | _, _, .stateDelete _ _ _ _ rest, _, Q, r, k, _, hr, hk => TStmts.denoteD_inv rest Q r k _ hr hk
    | _, _, .callVoid _ _ _ rest, _, Q, r, k, _, hr, hk => TStmts.denoteD_inv rest Q r k _ hr hk
    | _, _, .ite _ yes no rest, _, Q, r, k, ρ, hr, hk => by
      have hk' := hk.normal fun ρ' => TStmts.denoteD_inv rest Q r k ρ' hr hk
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_inv yes Q r _ ρ hr hk'
      · exact TStmts.denoteD_inv no Q r _ ρ hr hk'
    | _, _, .block body rest, _, Q, r, k, ρ, hr, hk => by
      have hk' := hk.normal fun ρ' => TStmts.denoteD_inv rest Q r k ρ' hr hk
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_inv body Q r _ ρ hr hk'
    | _, _, .ifNull v _ yes no rest, _, Q, r, k, ρ, hr, hk => by
      have hk' := hk.normal fun ρ' => TStmts.denoteD_inv rest Q r k ρ' hr hk
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_inv yes Q r _ ρ hr hk'
      · exact TStmts.denoteD_inv no Q r _ _ hr (K.Inv.map _ hk')
    | _, _, .ifNotNull v _ yes no rest, _, Q, r, k, ρ, hr, hk => by
      have hk' := hk.normal fun ρ' => TStmts.denoteD_inv rest Q r k ρ' hr hk
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_inv no Q r _ ρ hr hk'
      · exact TStmts.denoteD_inv yes Q r _ _ hr (K.Inv.map _ hk')
    | _, _, .ifNullExit v _ yes rest, _, Q, r, k, ρ, hr, hk => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_inv yes Q r k ρ hr hk
      · exact TStmts.denoteD_inv rest Q r _ _ hr (K.Inv.map _ hk)
    | _, _, .switchG v _ arms rest, _, Q, r, k, ρ, hr, hk => by
      have hrest := fun ρ' => TStmts.denoteD_inv rest Q r k ρ' hr hk
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, hu, Variants.elim_inj]
      exact TArms.denoteD_inv arms Q r _ ρ i y _ hr (fun ρ' => ⟨hrest ρ', hrest ρ', (hk ρ').2.2⟩) (hrest ρ)
    | _, _, .forOf _ _ body rest, _, Q, r, k, ρ, hr, hk => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_inv rest Q r k _ hr hk
      · exact forIn_inv (fun _ => True) Q
          (fun y n e s _ hn he => TStmts.denoteD_inv body Q r _ (y, s) hr
            fun σ' => ⟨hn _ trivial, he _ trivial, hn _ trivial⟩)
          (fun ρ' _ => TStmts.denoteD_inv rest Q r k ρ' hr hk) _ ρ trivial
    | _, _, .forEntries _ _ _ body rest, _, Q, r, k, ρ, hr, hk => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_inv rest Q r k _ hr hk
      · exact forIn_inv (fun _ => True) Q
          (fun (p : _ × Nat) n e s _ hn he => TStmts.denoteD_inv body Q r _ (p.1, (p.2 : Int), s) hr
            fun σ' => ⟨hn _ trivial, he _ trivial, hn _ trivial⟩)
          (fun ρ' _ => TStmts.denoteD_inv rest Q r k ρ' hr hk) _ ρ trivial
    | _, _, .forRange _ _ body rest, _, Q, r, k, ρ, hr, hk => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_inv rest Q r k _ hr hk
      · exact forIn_inv (fun _ => True) Q
          (fun j n e s _ hn he => TStmts.denoteD_inv body Q r _ (j, s) hr
            fun σ' => ⟨hn _ trivial, he _ trivial, hn _ trivial⟩)
          (fun ρ' _ => TStmts.denoteD_inv rest Q r k ρ' hr hk) _ ρ trivial
    | _, _, .whileLoop _ body rest, _, Q, r, k, ρ, hr, hk => by
      simp only [TStmts.denoteD]
      exact whileDo_inv (fun _ => True) Q
        (fun n e s _ _ hn he => TStmts.denoteD_inv body Q r _ s hr
          fun σ' => ⟨hn _ trivial, he _ trivial, hn _ trivial⟩)
        (fun ρ' _ => TStmts.denoteD_inv rest Q r k ρ' hr hk) ρ trivial

  theorem TArms.firstD_inv {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (Q : R → Prop) (r : τ.denote → R) (k : K Γ R) (ρ : Γ.denote),
      (∀ v, Q (r v)) → K.Inv Q k → Q (arms.firstD fs r k ρ)
    | .nil, _, _, _, _, ρ, _, hk => (hk ρ).1
    | .empty _ rest, _, Q, r, k, ρ, hr, hk => TArms.firstD_inv rest Q r k ρ hr hk
    | .wide _ body _, _, Q, r, k, ρ, hr, hk => TStmts.denoteD_inv body Q r k ρ hr hk
    | .narrow .., _, _, _, _, ρ, _, hk => (hk ρ).1

  theorem TArms.denoteD_inv {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (Q : R → Prop) (r : τ.denote → R) (k : K Γ R) (ρ : Γ.denote)
      {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d : R),
      (∀ v, Q (r v)) → K.Inv Q k → Q d → Q (arms.denoteD fs r k ρ i y d)
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, _, Q, r, k, ρ, _, _, i, y, d, hr, hk, hd => by
      simp only [TArms.denoteD]
      split
      · exact TArms.firstD_inv rest Q r k ρ hr hk
      · refine TArms.denoteD_inv rest Q r k ρ i y _ hr hk ?_
        split
        · exact TArms.firstD_inv rest Q r k ρ hr hk
        · exact hd
    | .wide l body rest, _, Q, r, k, ρ, _, _, i, y, d, hr, hk, hd => by
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_inv body Q r k ρ hr hk
      · refine TArms.denoteD_inv rest Q r k ρ i y _ hr hk ?_
        split
        · exact TStmts.denoteD_inv body Q r k ρ hr hk
        · exact hd
    | .narrow i' body rest, _, Q, r, k, ρ, _, _, i, y, d, hr, hk, hd => by
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_inv body Q r _ _ hr (K.Inv.map _ hk)
      · exact TArms.denoteD_inv rest Q r k ρ i y d hr hk hd
end

/-! ## Without a `continue` of its own -/

mutual
  /-- Without a `continue` of its own, the continue continuation is irrelevant. -/
  theorem TStmts.denoteD_noCont : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {R : Type} (r : τ.denote → R)
      (k k' : K Γ R), k.normal = k'.normal → k.brk = k'.brk → st.noCont = true → ∀ ρ,
      st.denoteD fs r k ρ = st.denoteD fs r k' ρ
    | _, _, .nil, _, _, _, _, hn, _, _, ρ => by simp only [TStmts.denoteD, hn]
    | _, _, .brk _, _, _, _, _, _, hb, _, ρ => by simp only [TStmts.denoteD, hb]
    | _, _, .cont _, _, _, _, _, _, _, h, _ => by simp [TStmts.noCont] at h
    | _, _, .ret _ _, _, _, _, _, _, _, _, _ => rfl
    | _, _, .retVoid _ _, _, _, _, _, _, _, _, _ => rfl
    | _, _, .const _ e rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_noCont rest r _ _ (by simp [hn]) (by simp [hb]) h _
    | _, _, .let_ _ e rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_noCont rest r _ _ (by simp [hn]) (by simp [hb]) h _
    | _, _, .assign _ e rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noCont rest r k k' hn hb h _
    | _, _, .stateSet _ _ _ _ _ rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noCont rest r k k' hn hb h _
    | _, _, .stateDelete _ _ _ _ rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noCont rest r k k' hn hb h _
    | _, _, .callVoid _ _ _ rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noCont rest r k k' hn hb h _
    | _, _, .ite c yes no rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h.2)
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noCont yes r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
          rfl hb h.1.1 ρ
      · exact TStmts.denoteD_noCont no r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
          rfl hb h.1.2 ρ
    | _, _, .block body rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h.2)
      simp only [TStmts.denoteD, e]
      exact TStmts.denoteD_noCont body r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
        rfl hb h.1 ρ
    | _, _, .ifNull v _ yes no rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h.2)
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noCont yes r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
          rfl hb h.1.1 ρ
      · exact TStmts.denoteD_noCont no r (K.map (v.widen some) { k with normal := rest.denoteD fs r k' })
          (K.map (v.widen some) { k' with normal := rest.denoteD fs r k' }) rfl (by simp [hb]) h.1.2 _
    | _, _, .ifNotNull v _ yes no rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h.2)
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noCont yes r (K.map (v.widen some) { k with normal := rest.denoteD fs r k' })
          (K.map (v.widen some) { k' with normal := rest.denoteD fs r k' }) rfl (by simp [hb]) h.1.1 _
      · exact TStmts.denoteD_noCont no r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
          rfl hb h.1.2 ρ
    | _, _, .ifNullExit v _ yes rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_noCont yes r k k' hn hb h.1 ρ
      · exact TStmts.denoteD_noCont rest r _ _ (by simp [hn]) (by simp [hb]) h.2 _
    | _, _, .switchG v _ arms rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h.2)
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, hu, Variants.elim_inj, e]
      exact TArms.denoteD_noCont arms r { k with normal := rest.denoteD fs r k', brk := rest.denoteD fs r k' }
        { k' with normal := rest.denoteD fs r k', brk := rest.denoteD fs r k' } rfl rfl h.1 ρ i y _
    | _, _, .forOf _ a body rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h)
      simp only [TStmts.denoteD, e]
    | _, _, .forEntries _ _ a body rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h)
      simp only [TStmts.denoteD, e]
    | _, _, .forRange _ v body rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h)
      simp only [TStmts.denoteD, e]
    | _, _, .whileLoop c body rest, _, r, k, k', hn, hb, h, ρ => by
      simp only [TStmts.noCont] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noCont rest r k k' hn hb h)
      simp only [TStmts.denoteD, e]

  theorem TArms.firstD_noCont {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r : τ.denote → R) (k k' : K Γ R), k.normal = k'.normal →
      k.brk = k'.brk → arms.noCont = true → ∀ ρ, arms.firstD fs r k ρ = arms.firstD fs r k' ρ
    | .nil, _, _, _, _, hn, _, _, ρ => by simp only [TArms.firstD, hn]
    | .empty _ rest, _, r, k, k', hn, hb, h, ρ => TArms.firstD_noCont rest r k k' hn hb h ρ
    | .wide _ body _, _, r, k, k', hn, hb, h, ρ => by
      simp only [TArms.noCont, Bool.and_eq_true] at h
      exact TStmts.denoteD_noCont body r k k' hn hb h.1 ρ
    | .narrow .., _, _, _, _, hn, _, _, ρ => by simp only [TArms.firstD, hn]

  theorem TArms.denoteD_noCont {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r : τ.denote → R) (k k' : K Γ R), k.normal = k'.normal →
      k.brk = k'.brk → arms.noCont = true → ∀ (ρ : Γ.denote) {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds)
      (y : fds.denote) (d : R), arms.denoteD fs r k ρ i y d = arms.denoteD fs r k' ρ i y d
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
    | .empty l rest, _, r, k, k', hn, hb, h, ρ, _, _, i, y, d => by
      simp only [TArms.noCont] at h
      simp only [TArms.denoteD, TArms.firstD_noCont rest r k k' hn hb h ρ]
      split
      · rfl
      · exact TArms.denoteD_noCont rest r k k' hn hb h ρ i y _
    | .wide l body rest, _, r, k, k', hn, hb, h, ρ, _, _, i, y, d => by
      simp only [TArms.noCont, Bool.and_eq_true] at h
      simp only [TArms.denoteD, TStmts.denoteD_noCont body r k k' hn hb h.1 ρ]
      split
      · rfl
      · exact TArms.denoteD_noCont rest r k k' hn hb h.2 ρ i y _
    | .narrow i' body rest, _, r, k, k', hn, hb, h, ρ, _, _, i, y, d => by
      simp only [TArms.noCont, Bool.and_eq_true] at h
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_noCont body r _ _ (by simp [hn]) (by simp [hb]) h.1 _
      · exact TArms.denoteD_noCont rest r k k' hn hb h.2 ρ i y d
end

/-- A closed statement list's result depends only on its normal continuation. -/
theorem TStmts.denoteD_closed {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (hc : st.closed = true) {R : Type}
    (r r' : τ.denote → R) (k k' : K Γ R) (hn : k.normal = k'.normal) (ρ : Γ.denote) :
    st.denoteD fs r k ρ = st.denoteD fs r' k' ρ := by
  simp only [TStmts.closed, Bool.and_eq_true] at hc
  rw [TStmts.denoteD_noRet st r r' k ρ hc.1.1,
    TStmts.denoteD_noBrk st r' k { k with brk := k'.brk } rfl rfl hc.1.2 ρ]
  exact TStmts.denoteD_noCont st r' { k with brk := k'.brk } k' hn rfl hc.2 ρ

theorem TArms.denoteD_closed {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
    (arms : TArms Φ Γ τ v) (hc : arms.closed = true) {R : Type} (r r' : τ.denote → R) (k k' : K Γ R)
    (hn : k.normal = k'.normal) (hb : k.brk = k'.brk) (ρ : Γ.denote) {t : TagLit} {fds : Fields}
    (i : VIdx vs0 t fds) (y : fds.denote) (d : R) :
    arms.denoteD fs r k ρ i y d = arms.denoteD fs r' k' ρ i y d := by
  simp only [TArms.closed, Bool.and_eq_true] at hc
  rw [TArms.denoteD_noRet arms r r' k ρ i y d hc.1]
  exact TArms.denoteD_noCont arms r' k k' hn hb hc.2 ρ i y d

/-! ## The frame property -/

/-- What a direct loop body computes, from an environment, agrees with it outside the body's writes. -/
theorem agree_of_frame {Γ : Ctx} {m : Mask} (ρ' : Γ.denote) (run : (Γ.denote → Γ.denote) → Γ.denote)
    (hframe : ∀ g : Γ.denote → Γ.denote, (∀ z, Agree Γ m ρ' z → z = g z) → run id = run g)
    (hinv : ∀ g : Γ.denote → Γ.denote, (∀ z, Agree Γ m ρ' (g z)) → Agree Γ m ρ' (run g)) :
    Agree Γ m ρ' (run id) := by
  classical
  let g : Γ.denote → Γ.denote := fun z => if Agree Γ m ρ' z then z else ρ'
  rw [hframe g (fun z h => by simp [g, h])]
  exact hinv g fun z => by
    simp only [g]
    split
    · assumption
    · exact Agree.refl _ _ _

mutual
  /-- **Frame**: a statement list calls its continuations only on environments that agree with the current
  one outside the variables it assigns. -/
  theorem TStmts.denoteD_frame : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {m : Mask}, Mask.incl st.writes m →
      ∀ {R : Type} (r : τ.denote → R) (k k' : K Γ R) (ρ : Γ.denote), KAgree m ρ k k' →
      st.denoteD fs r k ρ = st.denoteD fs r k' ρ
    | _, _, .nil, _, _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1
    | _, _, .brk _, _, _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).2.1
    | _, _, .cont _, _, _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).2.2
    | _, _, .ret _ _, _, _, _, _, _, _, _, _ => rfl
    | _, _, .retVoid _ _, _, _, _, _, _, _, _, _ => rfl
    | _, _, .const _ e rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.incl_cons hm) r _ _ _ fun σ' h => hk σ'.2 (Agree.of_cons h)
    | _, _, .let_ _ e rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.incl_cons hm) r _ _ _ fun σ' h => hk σ'.2 (Agree.of_cons h)
    | _, _, .assign v e rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .stateSet v _ _ _ _ rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .stateDelete v _ _ _ rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .callVoid _ v _ rest, m, hm, _, r, k, k', ρ, hk => by
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .ite c yes no rest, m, hm, _, r, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) r k k' ρ' (KAgree.of_agree h hk)
      have hk' : KAgree m ρ { k with normal := rest.denoteD fs r k } { k' with normal := rest.denoteD fs r k' } :=
        fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_frame yes (Mask.or_incl_left hm) r _ _ ρ hk'
      · exact TStmts.denoteD_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) r _ _ ρ hk'
    | _, _, .block body rest, m, hm, _, r, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.denoteD]
      exact TStmts.denoteD_frame body (Mask.or_incl_left hm) r _ _ ρ fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
    | _, _, .ifNull v _ yes no rest, m, hm, _, r, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) r k k' ρ' (KAgree.of_agree h hk)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_frame yes (Mask.or_incl_left hm) r _ _ ρ fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      · exact TStmts.denoteD_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) r _ _ _ fun ρn h =>
          have hw := Var.agree_widen v some ρ y ρn h hv.symm
          ⟨hrest _ hw, (hk _ hw).2⟩
    | _, _, .ifNotNull v _ yes no rest, m, hm, _, r, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) r k k' ρ' (KAgree.of_agree h hk)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) r _ _ ρ
          fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      · exact TStmts.denoteD_frame yes (Mask.or_incl_left hm) r _ _ _ fun ρn h =>
          have hw := Var.agree_widen v some ρ y ρn h hv.symm
          ⟨hrest _ hw, (hk _ hw).2⟩
    | _, _, .ifNullExit v _ yes rest, m, hm, _, r, k, k', ρ, hk => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, hv]
      · exact TStmts.denoteD_frame yes (Mask.or_incl_left hm) r k k' ρ hk
      · exact TStmts.denoteD_frame rest (Mask.or_incl_right hm) r _ _ _ fun ρn h =>
          hk _ (Var.agree_widen v some ρ y ρn h hv.symm)
    | _, _, .switchG v _ arms rest, m, hm, _, r, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, hu, Variants.elim_inj]
      exact TArms.denoteD_frame arms (Mask.or_incl_left hm) r _ _ ρ i y _ _ hu
        (fun ρ' h => ⟨hrest ρ' h, hrest ρ' h, (hk ρ' h).2.2⟩) (hrest ρ (Agree.refl _ _ ρ))
    | _, _, .forOf _ a body rest, m, hm, _, r, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: m) := Mask.incl_cons (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.denoteD]
      split
      · refine hrest _ (foldl_agree _ (fun ρ' y => ?_) _ ρ)
        exact agree_of_frame ρ' (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all g)) (y, ρ'))
          (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
            have e := hg _ (Agree.of_cons h); ⟨e, e, e⟩)
          (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
      · exact forIn_frame _ (fun y n n' e e' ρ' h hne => TStmts.denoteD_frame body hb r _ _ (y, ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .forEntries _ _ a body rest, m, hm, _, r, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: true :: m) := Mask.incl_cons₂ (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.denoteD]
      split
      · refine hrest _ (foldl_agree _ (fun ρ' (p : _ × Nat) => ?_) _ ρ)
        exact agree_of_frame ρ'
          (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.map Prod.snd (K.all g))) (p.1, (p.2 : Int), ρ'))
          (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
            have e := hg _ (Agree.of_cons₂ h); ⟨e, e, e⟩)
          (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
      · exact forIn_frame _ (fun (p : _ × Nat) n n' e e' ρ' h hne =>
            TStmts.denoteD_frame body hb r _ _ (p.1, (p.2 : Int), ρ') fun σ' h' =>
              have h2 := Agree.trans h (Agree.of_cons₂ h')
              ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .forRange _ v body rest, m, hm, _, r, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: m) := Mask.incl_cons (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.denoteD]
      split
      · refine hrest _ (foldl_agree _ (fun ρ' j => ?_) _ ρ)
        exact agree_of_frame ρ' (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all g)) (j, ρ'))
          (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
            have e := hg _ (Agree.of_cons h); ⟨e, e, e⟩)
          (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
      · exact forIn_frame _ (fun j n n' e e' ρ' h hne => TStmts.denoteD_frame body hb r _ _ (j, ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .whileLoop c body rest, m, hm, _, r, k, k', ρ, hk => by
      have hb : Mask.incl body.writes m := Mask.or_incl_left hm
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.denoteD fs r k ρ' = rest.denoteD fs r k' ρ' := fun ρ' h =>
        TStmts.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.denoteD]
      rw [whileDo_def, whileDo_def]
      exact whileIn_frame _ _ (fun n n' e e' ρ' h hne => TStmts.denoteD_frame body hb r _ _ ρ' fun σ' h' =>
          have h2 := Agree.trans h h'
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ _ _ hrest hrest _ ρ (Agree.refl _ _ ρ)

  theorem TArms.firstD_frame {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {m : Mask}, Mask.incl arms.writes m → ∀ {R : Type} (r : τ.denote → R)
      (k k' : K Γ R) (ρ : Γ.denote), KAgree m ρ k k' → arms.firstD fs r k ρ = arms.firstD fs r k' ρ
    | .nil, _, _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1
    | .empty _ rest, _, hm, _, r, k, k', ρ, hk => TArms.firstD_frame rest hm r k k' ρ hk
    | .wide _ body _, _, hm, _, r, k, k', ρ, hk => TStmts.denoteD_frame body (Mask.or_incl_left hm) r k k' ρ hk
    | .narrow .., _, _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1

  theorem TArms.denoteD_frame {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {m : Mask}, Mask.incl arms.writes m → ∀ {R : Type} (r : τ.denote → R)
      (k k' : K Γ R) (ρ : Γ.denote) {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d d' : R),
      v.get ρ = i.inj y → KAgree m ρ k k' → d = d' → arms.denoteD fs r k ρ i y d = arms.denoteD fs r k' ρ i y d'
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, _, hm, _, r, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      have hf := TArms.firstD_frame rest hm r k k' ρ hk
      simp only [TArms.denoteD, hf]
      split
      · rfl
      · refine TArms.denoteD_frame rest hm r k k' ρ i y _ _ hv hk ?_
        split
        · rfl
        · exact hd
    | .wide l body rest, _, hm, _, r, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      have hf := TStmts.denoteD_frame body (Mask.or_incl_left hm) r k k' ρ hk
      simp only [TArms.denoteD, hf]
      split
      · rfl
      · refine TArms.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ i y _ _ hv hk ?_
        split
        · rfl
        · exact hd
    | .narrow i' body rest, _, hm, _, r, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      rcases hp : i'.proj (i.inj y) with _ | y' <;> simp only [TArms.denoteD, hp]
      · exact TArms.denoteD_frame rest (Mask.or_incl_right hm) r k k' ρ i y d d' hv hk hd
      · exact TStmts.denoteD_frame body (Mask.or_incl_left hm) r _ _ _ fun ρn h =>
          hk _ (Var.agree_widen v (fun (z : _ × _) => i'.inj z.2) ρ ((), y') ρn h
            ((VIdx.inj_of_proj i' _ y' hp).trans hv.symm))
end

/-! ## Loops over states -/

/-- A fold over environments whose steps change only the mask's positions is a fold over states. -/
theorem foldl_proj {α : Type} (Γ : Ctx) (m : Mask) (ρ : Γ.denote) (F : Γ.denote → α → Γ.denote)
    (hF : ∀ ρ' y, Agree Γ m ρ' (F ρ' y)) : ∀ (xs : List α) (ρ' : Γ.denote), Agree Γ m ρ ρ' →
    xs.foldl F ρ' =
      Ctx.merge Γ m ρ (xs.foldl (fun s y => Ctx.proj Γ m (F (Ctx.merge Γ m ρ s) y)) (Ctx.proj Γ m ρ'))
  | [], ρ', h => (Ctx.merge_proj Γ m ρ ρ' h).symm
  | y :: ys, ρ', h => by
    simp only [List.foldl_cons]
    rw [Ctx.merge_proj Γ m ρ ρ' h]
    exact foldl_proj Γ m ρ F hF ys _ (Agree.trans h (hF ρ' y))

/-- A loop whose iterations call their continuations only on environments agreeing outside the mask is
a loop over states. -/
theorem forIn_proj {α R : Type} (Γ : Ctx) (m : Mask) (ρ : Γ.denote)
    (step : α → (Γ.denote → R) → (Γ.denote → R) → Γ.denote → R)
    (hs : ∀ y n n' e e' ρ', Agree Γ m ρ ρ' → (∀ ρ'', Agree Γ m ρ ρ'' → n ρ'' = n' ρ'' ∧ e ρ'' = e' ρ'') →
      step y n e ρ' = step y n' e' ρ')
    (E : Γ.denote → R) : ∀ (xs : List α) (ρ' : Γ.denote), Agree Γ m ρ ρ' →
    forIn xs step E ρ' =
      forIn xs (fun y n e s => step y (n ∘ Ctx.proj Γ m) (e ∘ Ctx.proj Γ m) (Ctx.merge Γ m ρ s))
        (fun s => E (Ctx.merge Γ m ρ s)) (Ctx.proj Γ m ρ')
  | [], ρ', h => by rw [forIn_nil, forIn_nil, Ctx.merge_proj Γ m ρ ρ' h]
  | y :: ys, ρ', h => by
    rw [forIn_cons, forIn_cons]
    rw [Ctx.merge_proj Γ m ρ ρ' h]
    exact hs y _ _ _ _ ρ' h fun ρ'' h' =>
      ⟨forIn_proj Γ m ρ step hs E ys ρ'' h', by simp only [Function.comp, Ctx.merge_proj Γ m ρ ρ'' h']⟩

theorem whileIn_proj {R : Type} (Γ : Ctx) (m : Mask) (ρ : Γ.denote) (cond : Γ.denote → Bool)
    (step : (Γ.denote → R) → (Γ.denote → R) → Γ.denote → R)
    (hs : ∀ n n' e e' ρ', Agree Γ m ρ ρ' → (∀ ρ'', Agree Γ m ρ ρ'' → n ρ'' = n' ρ'' ∧ e ρ'' = e' ρ'') →
      step n e ρ' = step n' e' ρ')
    (E stuck : Γ.denote → R) : ∀ (n : Nat) (ρ' : Γ.denote), Agree Γ m ρ ρ' →
    whileIn n cond step E stuck ρ' =
      whileIn n (fun s => cond (Ctx.merge Γ m ρ s))
        (fun n e s => step (n ∘ Ctx.proj Γ m) (e ∘ Ctx.proj Γ m) (Ctx.merge Γ m ρ s))
        (fun s => E (Ctx.merge Γ m ρ s)) (fun s => stuck (Ctx.merge Γ m ρ s)) (Ctx.proj Γ m ρ')
  | 0, ρ', h => by rw [whileIn_zero, whileIn_zero, Ctx.merge_proj Γ m ρ ρ' h]
  | n + 1, ρ', h => by
    rw [whileIn_succ, whileIn_succ]
    rw [Ctx.merge_proj Γ m ρ ρ' h]
    split
    · exact hs _ _ _ _ ρ' h fun ρ'' h' =>
        ⟨whileIn_proj Γ m ρ cond step hs E stuck n ρ'' h', by simp only [Function.comp, Ctx.merge_proj Γ m ρ ρ'' h']⟩
    · rfl

/-- A closed statement list's result, through its normal continuation `J`: `J` of the state it leaves. The
list runs in `σ₀`, a context `Δ` that `w` embeds into `Γ` (the identity, or a narrowing undone). -/
theorem TStmts.denoteD_value {Δ Γ : Ctx} {τ : Ty} (st : TStmts Φ Δ τ) (hc : st.closed = true) {mΔ m : Mask}
    (hm : Mask.incl st.writes mΔ) (w : Δ.denote → Γ.denote) (ρ : Γ.denote) (σ₀ : Δ.denote)
    (hw : ∀ σ', Agree Δ mΔ σ₀ σ' → Agree Γ m ρ (w σ')) {R : Type} (r : τ.denote → R) (k : K Γ R)
    (J : Γ.denote → R) (r₀ : τ.denote → (Γ.sub m).tup) :
    st.denoteD fs r (K.map w { k with normal := J }) σ₀ =
      J (Ctx.merge Γ m ρ (st.denoteD fs r₀ (K.map w (K.all (Ctx.proj Γ m))) σ₀)) := by
  rw [TStmts.denoteD_nat st (fun s => J (Ctx.merge Γ m ρ s)) r₀ _ σ₀,
    TStmts.denoteD_frame st hm r (K.map w { k with normal := J })
      (K.map w { k with normal := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')) }) σ₀
      (fun σ' h => ⟨by simp only [Function.comp, Ctx.merge_proj Γ m ρ _ (hw σ' h)], rfl, rfl⟩)]
  exact TStmts.denoteD_closed st hc _ _ (K.map w { k with normal := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')) })
    ((K.map w (K.all (Ctx.proj Γ m))).post fun s => J (Ctx.merge Γ m ρ s)) rfl σ₀

/-- The same for `switch` cases that always go on after the `switch`. -/
theorem TArms.denoteD_value {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
    (arms : TArms Φ Γ τ v) (hc : arms.closed = true) {m : Mask} (hm : Mask.incl arms.writes m) (ρ : Γ.denote)
    {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (hv : v.get ρ = i.inj y) {R : Type}
    (r : τ.denote → R) (k : K Γ R) (J : Γ.denote → R) (r₀ : τ.denote → (Γ.sub m).tup) :
    arms.denoteD fs r { k with normal := J, brk := J } ρ i y (J ρ) =
      J (Ctx.merge Γ m ρ (arms.denoteD fs r₀ (K.all (Ctx.proj Γ m)) ρ i y (Ctx.proj Γ m ρ))) := by
  rw [TArms.denoteD_nat arms (fun s => J (Ctx.merge Γ m ρ s)) r₀ _ ρ i y,
    TArms.denoteD_frame arms hm r { k with normal := J, brk := J }
      { k with normal := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')),
               brk := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')) } ρ i y _ (J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ))) hv
      (fun σ' h => by
        have e : J σ' = J (Ctx.merge Γ m ρ (Ctx.proj Γ m σ')) := by rw [Ctx.merge_proj Γ m ρ σ' h]
        exact ⟨e, e, rfl⟩)
      (by rw [Ctx.merge_proj Γ m ρ ρ (Agree.refl _ _ ρ)])]
  exact TArms.denoteD_closed arms hc _ _
    { k with normal := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')),
             brk := fun ρ' => J (Ctx.merge Γ m ρ (Ctx.proj Γ m ρ')) }
    ((K.all (Ctx.proj Γ m)).post fun s => J (Ctx.merge Γ m ρ s)) rfl rfl ρ i y _

/-! ## The denotation with states is the direct-style denotation -/

mutual
  theorem TStmts.denoteD_eq_R : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {R : Type} (r : τ.denote → R)
      (k : K Γ R) (ρ : Γ.denote), st.denoteD fs r k ρ = st.denoteR fs r k ρ
    | _, _, .nil, _, _, _, _ => rfl
    | _, _, .brk _, _, _, _, _ => rfl
    | _, _, .cont _, _, _, _, _ => rfl
    | _, _, .ret _ _, _, _, _, _ => rfl
    | _, _, .retVoid _ _, _, _, _, _ => rfl
    | _, _, .const _ e rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .let_ _ e rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .assign _ e rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .stateSet _ _ _ _ _ rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .stateDelete _ _ _ _ rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .callVoid _ _ _ rest, _, r, k, ρ => by
      simp only [TStmts.denoteD, TStmts.denoteR]; exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .block body rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      simp only [TStmts.denoteD, TStmts.denoteR, e]
      exact TStmts.denoteD_eq_R body r _ ρ
    | _, _, .ite c yes no rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have ey : ∀ {R' : Type} (r' : _ → R') k' ρ', yes.denoteR fs r' k' ρ' = yes.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R yes r' k' ρ').symm
      have en : ∀ {R' : Type} (r' : _ → R') k' ρ', no.denoteR fs r' k' ρ' = no.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R no r' k' ρ').symm
      simp only [TStmts.denoteD, TStmts.denoteR, e, ey, en]
      by_cases hc : (yes.closed && no.closed) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true] at hc
        split
        · exact TStmts.denoteD_value yes hc.1 (Mask.incl_trans (Mask.incl_trans (Mask.incl_refl _)
            (fun i h => by rw [Mask.getD_or, h]; rfl)) (Mask.incl_refl _)) id ρ ρ (fun _ h => h) r k _ _
        · exact TStmts.denoteD_value no hc.2 (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) id ρ ρ
            (fun _ h => h) r k _ _
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
    | _, _, .ifNull v _ yes no rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have ey : ∀ {R' : Type} (r' : _ → R') k' ρ', yes.denoteR fs r' k' ρ' = yes.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R yes r' k' ρ').symm
      have en : ∀ {R' : Type} (r' : _ → R') k' ρ', no.denoteR fs r' k' ρ' = no.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R no r' k' ρ').symm
      simp only [TStmts.denoteD, TStmts.denoteR, e, ey, en]
      by_cases hc : (yes.closed && no.closed) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true] at hc
        rcases hv : v.get ρ with _ | y <;> simp only []
        · exact TStmts.denoteD_value yes hc.1 (fun i h => by rw [Mask.getD_or, h]; rfl) id ρ ρ (fun _ h => h) r k _ _
        · exact TStmts.denoteD_value no hc.2 (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) (v.widen some) ρ
            (v.narrowVal ρ y) (fun σ' h => Var.agree_widen v some ρ y σ' h hv.symm) r k _ _
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rcases hv : v.get ρ with _ | y <;> rfl
    | _, _, .ifNotNull v _ yes no rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have ey : ∀ {R' : Type} (r' : _ → R') k' ρ', yes.denoteR fs r' k' ρ' = yes.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R yes r' k' ρ').symm
      have en : ∀ {R' : Type} (r' : _ → R') k' ρ', no.denoteR fs r' k' ρ' = no.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R no r' k' ρ').symm
      simp only [TStmts.denoteD, TStmts.denoteR, e, ey, en]
      by_cases hc : (yes.closed && no.closed) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true] at hc
        rcases hv : v.get ρ with _ | y <;> simp only []
        · exact TStmts.denoteD_value no hc.2 (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) id ρ ρ
            (fun _ h => h) r k _ _
        · exact TStmts.denoteD_value yes hc.1 (fun i h => by rw [Mask.getD_or, h]; rfl) (v.widen some) ρ
            (v.narrowVal ρ y) (fun σ' h => Var.agree_widen v some ρ y σ' h hv.symm) r k _ _
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rcases hv : v.get ρ with _ | y <;> rfl
    | _, _, .ifNullExit v _ yes rest, _, r, k, ρ => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denoteD, TStmts.denoteR, hv]
      · exact TStmts.denoteD_eq_R yes r k ρ
      · exact TStmts.denoteD_eq_R rest r _ _
    | _, _, .switchG v _ arms rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have ea : ∀ {R' : Type} (r' : _ → R') k' ρ' {t fds} (i : VIdx _ t fds) y d,
          arms.denoteR fs r' k' ρ' i y d = arms.denoteD fs r' k' ρ' i y d :=
        @fun _ r' k' ρ' _ _ i y d => (TArms.denoteD_eq_R arms r' k' ρ' i y d).symm
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, TStmts.denoteR, hu, Variants.elim_inj, e, ea]
      by_cases hc : arms.closed = true
      · simp only [hc, ↓reduceIte]
        exact TArms.denoteD_value arms hc (Mask.incl_refl _) ρ i y hu r k _ _
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
    | _, _, .forOf _ a body rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have eb : ∀ {R' : Type} (r' : _ → R') k' ρ', body.denoteR fs r' k' ρ' = body.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R body r' k' ρ').symm
      have hb : Mask.incl body.writes (true :: body.writes.tail) := Mask.incl_cons (Mask.incl_refl _)
      simp only [TStmts.denoteD, TStmts.denoteR, e, eb]
      split
      · congr 1
        refine (foldl_proj _ body.writes.tail ρ _ (fun ρ' y => ?_) _ ρ (Agree.refl _ _ ρ)).trans ?_
        · exact agree_of_frame ρ' (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all g)) (y, ρ'))
            (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
              have e := hg _ (Agree.of_cons h); ⟨e, e, e⟩)
            (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
        · congr 1
          refine congrArg (fun f => List.foldl f _ _) (funext fun s => funext fun y => ?_)
          rw [TStmts.denoteD_nat body (Ctx.proj _ _) _ _ (y, _)]
          congr 1
          all_goals first | rfl | (funext _; exact Ctx.proj_merge _ _ _ _)
      · exact forIn_proj _ _ ρ _ (fun y n n' e e' ρ' h hne => TStmts.denoteD_frame body hb r _ _ (y, ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .forEntries _ _ a body rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have eb : ∀ {R' : Type} (r' : _ → R') k' ρ', body.denoteR fs r' k' ρ' = body.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R body r' k' ρ').symm
      have hb : Mask.incl body.writes (true :: true :: body.writes.tail.tail) := Mask.incl_cons₂ (Mask.incl_refl _)
      simp only [TStmts.denoteD, TStmts.denoteR, e, eb]
      split
      · congr 1
        refine (foldl_proj _ body.writes.tail.tail ρ _ (fun ρ' (p : _ × Nat) => ?_) _ ρ (Agree.refl _ _ ρ)).trans ?_
        · exact agree_of_frame ρ'
            (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.map Prod.snd (K.all g))) (p.1, (p.2 : Int), ρ'))
            (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
              have e := hg _ (Agree.of_cons₂ h); ⟨e, e, e⟩)
            (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
        · congr 1
          refine congrArg (fun f => List.foldl f _ _) (funext fun s => funext fun (p : _ × Nat) => ?_)
          rw [TStmts.denoteD_nat body (Ctx.proj _ _) _ _ (p.1, (p.2 : Int), _)]
          congr 1
          all_goals first | rfl | (funext _; exact Ctx.proj_merge _ _ _ _)
      · exact forIn_proj _ _ ρ _ (fun (p : _ × Nat) n n' e e' ρ' h hne =>
            TStmts.denoteD_frame body hb r _ _ (p.1, (p.2 : Int), ρ') fun σ' h' =>
              have h2 := Agree.trans h (Agree.of_cons₂ h')
              ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .forRange _ v body rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have eb : ∀ {R' : Type} (r' : _ → R') k' ρ', body.denoteR fs r' k' ρ' = body.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R body r' k' ρ').symm
      have hb : Mask.incl body.writes (true :: body.writes.tail) := Mask.incl_cons (Mask.incl_refl _)
      simp only [TStmts.denoteD, TStmts.denoteR, e, eb]
      split
      · congr 1
        refine (foldl_proj _ body.writes.tail ρ _ (fun ρ' j => ?_) _ ρ (Agree.refl _ _ ρ)).trans ?_
        · exact agree_of_frame ρ' (fun g => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all g)) (j, ρ'))
            (fun g hg => TStmts.denoteD_frame body hb _ _ _ _ fun σ' h =>
              have e := hg _ (Agree.of_cons h); ⟨e, e, e⟩)
            (fun g hg => TStmts.denoteD_inv body _ _ _ _ (fun _ => Agree.refl _ _ _) fun σ' => ⟨hg _, hg _, hg _⟩)
        · congr 1
          refine congrArg (fun f => List.foldl f _ _) (funext fun s => funext fun j => ?_)
          rw [TStmts.denoteD_nat body (Ctx.proj _ _) _ _ (j, _)]
          congr 1
          all_goals first | rfl | (funext _; exact Ctx.proj_merge _ _ _ _)
      · exact forIn_proj _ _ ρ _ (fun j n n' e e' ρ' h hne => TStmts.denoteD_frame body hb r _ _ (j, ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .whileLoop c body rest, _, r, k, ρ => by
      have e : rest.denoteR fs r k = rest.denoteD fs r k := funext fun ρ' => (TStmts.denoteD_eq_R rest r k ρ').symm
      have eb : ∀ {R' : Type} (r' : _ → R') k' ρ', body.denoteR fs r' k' ρ' = body.denoteD fs r' k' ρ' :=
        fun r' k' ρ' => (TStmts.denoteD_eq_R body r' k' ρ').symm
      simp only [TStmts.denoteD, TStmts.denoteR, e, eb]
      rw [whileDo_def, whileDo_def]
      exact whileIn_proj _ _ ρ _ _ (fun n n' e e' ρ' h hne =>
          TStmts.denoteD_frame body (Mask.incl_refl _) r _ _ ρ' fun σ' h' =>
            have h2 := Agree.trans h h'
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ _ ρ (Agree.refl _ _ ρ)

  theorem TArms.firstD_eq_R {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r : τ.denote → R) (k : K Γ R) (ρ : Γ.denote),
      arms.firstD fs r k ρ = arms.firstR fs r k ρ
    | .nil, _, _, _, _ => rfl
    | .empty _ rest, _, r, k, ρ => TArms.firstD_eq_R rest r k ρ
    | .wide _ body _, _, r, k, ρ => TStmts.denoteD_eq_R body r k ρ
    | .narrow .., _, _, _, _ => rfl

  theorem TArms.denoteD_eq_R {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r : τ.denote → R) (k : K Γ R) (ρ : Γ.denote) {t : TagLit} {fds : Fields}
      (i : VIdx vs0 t fds) (y : fds.denote) (d : R), arms.denoteD fs r k ρ i y d = arms.denoteR fs r k ρ i y d
    | .nil, _, _, _, _, _, _, _, _, _ => rfl
    | .empty l rest, _, r, k, ρ, t, _, i, y, d => by
      simp only [TArms.denoteD, TArms.denoteR, TArms.firstD_eq_R rest r k ρ]
      split
      · rfl
      · exact TArms.denoteD_eq_R rest r k ρ i y _
    | .wide l body rest, _, r, k, ρ, t, _, i, y, d => by
      simp only [TArms.denoteD, TArms.denoteR, TStmts.denoteD_eq_R body r k ρ]
      split
      · rfl
      · exact TArms.denoteD_eq_R rest r k ρ i y _
    | .narrow i' body rest, _, r, k, ρ, t, _, i, y, d => by
      rcases hp : i'.proj (i.inj y) with _ | y' <;> simp only [TArms.denoteD, TArms.denoteR, hp]
      · exact TArms.denoteD_eq_R rest r k ρ i y d
      · exact TStmts.denoteD_eq_R body r _ _
end

/-- **The denotation with states is the denotation**: for every function body, `denoteRFn` (states that
hold only the assigned variables) is `denoteFn`, which the general theorem is about. -/
theorem TStmts.denoteFn_eq_R {Γ : Ctx} {τ : Ty} (body : TStmts Φ Γ τ) : body.denoteFn fs = body.denoteRFn fs :=
  (TStmts.denoteFn_eq body).trans (funext fun ρ => TStmts.denoteD_eq_R body _ _ ρ)


/-! ## The safety condition with states -/

section
variable {ss : Φ.safety}

theorem whileSafe_frame {Γ : Ctx} {m : Mask} {ρ : Γ.denote} (cond : Γ.denote → Bool)
    (step : (Γ.denote → Bool) → (Γ.denote → Bool) → Γ.denote → Bool)
    (hs : ∀ n n' e e' ρ', Agree Γ m ρ ρ' → (∀ ρ'', Agree Γ m ρ ρ'' → n ρ'' = n' ρ'' ∧ e ρ'' = e' ρ'') →
      step n e ρ' = step n' e' ρ')
    (E E' : Γ.denote → Bool) (hE : ∀ ρ', Agree Γ m ρ ρ' → E ρ' = E' ρ') (ρ' : Γ.denote) (h : Agree Γ m ρ ρ') :
    whileSafe cond step E ρ' = whileSafe cond step E' ρ' := by
  rw [whileSafe_def, whileSafe_def]
  exact whileIn_frame cond step hs E E' _ _ hE (fun _ _ => rfl) _ ρ' h

mutual
  /-- **Frame** for safety conditions: a statement list calls its continuations only on environments that
  agree with the current one outside the variables it assigns. -/
  theorem TStmts.safe_frame : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {m : Mask}, Mask.incl st.writes m →
      ∀ (k k' : K Γ Bool) (ρ : Γ.denote), KAgree m ρ k k' → st.safe fs ss k ρ = st.safe fs ss k' ρ
    | _, _, .nil, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1
    | _, _, .brk _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).2.1
    | _, _, .cont _, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).2.2
    | _, _, .ret _ _, _, _, _, _, _, _ => rfl
    | _, _, .retVoid _ _, _, _, _, _, _, _ => rfl
    | _, _, .const _ e rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.incl_cons hm) _ _ _ fun σ' h => hk σ'.2 (Agree.of_cons h)
    | _, _, .let_ _ e rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.incl_cons hm) _ _ _ fun σ' h => hk σ'.2 (Agree.of_cons h)
    | _, _, .assign v e rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.or_incl_right hm) k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .stateSet v _ _ _ _ rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.or_incl_right hm) k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .stateDelete v _ _ _ rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.or_incl_right hm) k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .callVoid _ v _ rest, m, hm, k, k', ρ, hk => by
      simp only [TStmts.safe]; congr 1
      exact TStmts.safe_frame rest (Mask.or_incl_right hm) k k' _
        (KAgree.of_agree (Var.agree_set v (Mask.or_incl_left hm) ρ _) hk)
    | _, _, .ite c yes no rest, m, hm, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) k k' ρ' (KAgree.of_agree h hk)
      have hk' : KAgree m ρ { k with normal := rest.safe fs ss k } { k' with normal := rest.safe fs ss k' } :=
        fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      simp only [TStmts.safe]; congr 1
      split
      · exact TStmts.safe_frame yes (Mask.or_incl_left hm) _ _ ρ hk'
      · exact TStmts.safe_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) _ _ ρ hk'
    | _, _, .block body rest, m, hm, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.safe]
      exact TStmts.safe_frame body (Mask.or_incl_left hm) _ _ ρ fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
    | _, _, .ifNull v _ yes no rest, m, hm, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) k k' ρ' (KAgree.of_agree h hk)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, hv]
      · exact TStmts.safe_frame yes (Mask.or_incl_left hm) _ _ ρ fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      · exact TStmts.safe_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) _ _ _ fun ρn h =>
          have hw := Var.agree_widen v some ρ y ρn h hv.symm
          ⟨hrest _ hw, (hk _ hw).2⟩
    | _, _, .ifNotNull v _ yes no rest, m, hm, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right (Mask.or_incl_right hm)) k k' ρ' (KAgree.of_agree h hk)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, hv]
      · exact TStmts.safe_frame no (Mask.or_incl_left (Mask.or_incl_right hm)) _ _ ρ
          fun ρ' h => ⟨hrest ρ' h, (hk ρ' h).2⟩
      · exact TStmts.safe_frame yes (Mask.or_incl_left hm) _ _ _ fun ρn h =>
          have hw := Var.agree_widen v some ρ y ρn h hv.symm
          ⟨hrest _ hw, (hk _ hw).2⟩
    | _, _, .ifNullExit v _ yes rest, m, hm, k, k', ρ, hk => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, hv]
      · exact TStmts.safe_frame yes (Mask.or_incl_left hm) k k' ρ hk
      · exact TStmts.safe_frame rest (Mask.or_incl_right hm) _ _ _ fun ρn h =>
          hk _ (Var.agree_widen v some ρ y ρn h hv.symm)
    | _, _, .switchG v _ arms rest, m, hm, k, k', ρ, hk => by
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.safe, hu, Variants.elim_inj]
      exact TArms.safe_frame arms (Mask.or_incl_left hm) _ _ ρ i y _ _ hu
        (fun ρ' h => ⟨hrest ρ' h, hrest ρ' h, (hk ρ' h).2.2⟩) (hrest ρ (Agree.refl _ _ ρ))
    | _, _, .forOf _ a body rest, m, hm, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: m) := Mask.incl_cons (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.safe]; congr 1
      exact forIn_frame _ (fun y n n' e e' ρ' h hne => TStmts.safe_frame body hb _ _ (y, ρ') fun σ' h' =>
          have h2 := Agree.trans h (Agree.of_cons h')
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .forEntries _ _ a body rest, m, hm, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: true :: m) := Mask.incl_cons₂ (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.safe]; congr 1
      exact forIn_frame _ (fun (p : _ × Nat) n n' e e' ρ' h hne =>
          TStmts.safe_frame body hb _ _ (p.1, (p.2 : Int), ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons₂ h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .forRange _ v body rest, m, hm, k, k', ρ, hk => by
      have hb : Mask.incl body.writes (true :: m) := Mask.incl_cons (Mask.or_incl_left hm)
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.safe]
      exact forIn_frame _ (fun j n n' e e' ρ' h hne => TStmts.safe_frame body hb _ _ (j, ρ') fun σ' h' =>
          have h2 := Agree.trans h (Agree.of_cons h')
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest _ ρ (Agree.refl _ _ ρ)
    | _, _, .whileLoop c body rest, m, hm, k, k', ρ, hk => by
      have hb : Mask.incl body.writes m := Mask.or_incl_left hm
      have hrest : ∀ ρ', Agree _ m ρ ρ' → rest.safe fs ss k ρ' = rest.safe fs ss k' ρ' := fun ρ' h =>
        TStmts.safe_frame rest (Mask.or_incl_right hm) k k' ρ' (KAgree.of_agree h hk)
      simp only [TStmts.safe]
      exact whileSafe_frame _ _ (fun n n' e e' ρ' h hne => TStmts.safe_frame body hb _ _ ρ' fun σ' h' =>
          have h2 := Agree.trans h h'
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ hrest ρ (Agree.refl _ _ ρ)

  theorem TArms.firstSafe_frame {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {m : Mask}, Mask.incl arms.writes m →
      ∀ (k k' : K Γ Bool) (ρ : Γ.denote), KAgree m ρ k k' → arms.firstSafe fs ss k ρ = arms.firstSafe fs ss k' ρ
    | .nil, _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1
    | .empty _ rest, _, hm, k, k', ρ, hk => TArms.firstSafe_frame rest hm k k' ρ hk
    | .wide _ body _, _, hm, k, k', ρ, hk => TStmts.safe_frame body (Mask.or_incl_left hm) k k' ρ hk
    | .narrow .., _, _, _, _, ρ, hk => (hk ρ (Agree.refl _ _ ρ)).1

  theorem TArms.safe_frame {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {m : Mask}, Mask.incl arms.writes m →
      ∀ (k k' : K Γ Bool) (ρ : Γ.denote) {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d d' : Bool),
      v.get ρ = i.inj y → KAgree m ρ k k' → d = d' → arms.safe fs ss k ρ i y d = arms.safe fs ss k' ρ i y d'
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, _, hm, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      have hf := TArms.firstSafe_frame rest hm k k' ρ hk
      simp only [TArms.safe, hf]
      split
      · rfl
      · refine TArms.safe_frame rest hm k k' ρ i y _ _ hv hk ?_
        split
        · rfl
        · exact hd
    | .wide l body rest, _, hm, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      have hf := TStmts.safe_frame body (Mask.or_incl_left hm) k k' ρ hk
      simp only [TArms.safe, hf]
      split
      · rfl
      · refine TArms.safe_frame rest (Mask.or_incl_right hm) k k' ρ i y _ _ hv hk ?_
        split
        · rfl
        · exact hd
    | .narrow i' body rest, _, hm, k, k', ρ, _, _, i, y, d, d', hv, hk, hd => by
      rcases hp : i'.proj (i.inj y) with _ | y' <;> simp only [TArms.safe, hp]
      · exact TArms.safe_frame rest (Mask.or_incl_right hm) k k' ρ i y d d' hv hk hd
      · exact TStmts.safe_frame body (Mask.or_incl_left hm) _ _ _ fun ρn h =>
          hk _ (Var.agree_widen v (fun (z : _ × _) => i'.inj z.2) ρ ((), y') ρn h
            ((VIdx.inj_of_proj i' _ y' hp).trans hv.symm))
end

/-- Continuations through the join point of branches assigning `m` agree with the continuation itself. -/
theorem KAgree.join {Γ : Ctx} {m : Mask} {ρ : Γ.denote} (k : K Γ Bool) (after : Γ.denote → Bool) :
    KAgree m ρ { k with normal := after } { k with normal := Γ.join m ρ after } :=
  fun ρ' h => ⟨by simp only [Ctx.join, Ctx.merge_proj Γ m ρ ρ' h], rfl, rfl⟩

mutual
  theorem TStmts.safe_eq_R : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (k : K Γ Bool) (ρ : Γ.denote),
      st.safe fs ss k ρ = st.safeR fs ss k ρ
    | _, _, .nil, _, _ => rfl
    | _, _, .brk _, _, _ => rfl
    | _, _, .cont _, _, _ => rfl
    | _, _, .ret _ _, _, _ => rfl
    | _, _, .retVoid _ _, _, _ => rfl
    | _, _, .const _ e rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .let_ _ e rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .assign _ e rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .stateSet _ _ _ _ _ rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .stateDelete _ _ _ _ rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .callVoid _ _ _ rest, k, ρ => by
      simp only [TStmts.safe, TStmts.safeR, TStmts.safe_eq_R rest]
    | _, _, .block body rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      simp only [TStmts.safe, TStmts.safeR, e]
      exact TStmts.safe_eq_R body _ ρ
    | _, _, .ite c yes no rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have ey : ∀ k' ρ', yes.safeR fs ss k' ρ' = yes.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R yes k' ρ').symm
      have en : ∀ k' ρ', no.safeR fs ss k' ρ' = no.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R no k' ρ').symm
      simp only [TStmts.safe, TStmts.safeR, e, ey, en]
      congr 1
      split
      · exact TStmts.safe_frame yes (fun i h => by rw [Mask.getD_or, h]; rfl) _ _ ρ (KAgree.join k _)
      · exact TStmts.safe_frame no (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) _ _ ρ (KAgree.join k _)
    | _, _, .ifNull v _ yes no rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have ey : ∀ k' ρ', yes.safeR fs ss k' ρ' = yes.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R yes k' ρ').symm
      have en : ∀ k' ρ', no.safeR fs ss k' ρ' = no.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R no k' ρ').symm
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, TStmts.safeR, hv, e, ey, en]
      · exact TStmts.safe_frame yes (fun i h => by rw [Mask.getD_or, h]; rfl) _ _ ρ (KAgree.join k _)
      · exact TStmts.safe_frame no (m := Mask.or yes.writes no.writes)
          (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) _ _ _ fun σ' h =>
          have hw := Var.agree_widen v some ρ y σ' h hv.symm
          ⟨by simp only [Function.comp, Ctx.join, Ctx.merge_proj _ _ ρ _ hw], rfl, rfl⟩
    | _, _, .ifNotNull v _ yes no rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have ey : ∀ k' ρ', yes.safeR fs ss k' ρ' = yes.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R yes k' ρ').symm
      have en : ∀ k' ρ', no.safeR fs ss k' ρ' = no.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R no k' ρ').symm
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, TStmts.safeR, hv, e, ey, en]
      · exact TStmts.safe_frame no (fun i h => by rw [Mask.getD_or, h, Bool.or_true]) _ _ ρ (KAgree.join k _)
      · exact TStmts.safe_frame yes (m := Mask.or yes.writes no.writes)
          (fun i h => by rw [Mask.getD_or, h]; rfl) _ _ _ fun σ' h =>
          have hw := Var.agree_widen v some ρ y σ' h hv.symm
          ⟨by simp only [Function.comp, Ctx.join, Ctx.merge_proj _ _ ρ _ hw], rfl, rfl⟩
    | _, _, .ifNullExit v _ yes rest, k, ρ => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.safe, TStmts.safeR, hv]
      · exact TStmts.safe_eq_R yes k ρ
      · exact TStmts.safe_eq_R rest _ _
    | _, _, .switchG v _ arms rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have ea : ∀ k' ρ' {t fds} (i : VIdx _ t fds) y d, arms.safeR fs ss k' ρ' i y d = arms.safe fs ss k' ρ' i y d :=
        @fun k' ρ' _ _ i y d => (TArms.safe_eq_R arms k' ρ' i y d).symm
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.safe, TStmts.safeR, hu, Variants.elim_inj, e, ea]
      exact TArms.safe_frame arms (Mask.incl_refl _) _ _ ρ i y _ _ hu
        (fun ρ' h => ⟨by simp only [Ctx.join, Ctx.merge_proj _ _ ρ ρ' h],
          by simp only [Ctx.join, Ctx.merge_proj _ _ ρ ρ' h], rfl⟩) rfl
    | _, _, .forOf _ a body rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have eb : ∀ k' ρ', body.safeR fs ss k' ρ' = body.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R body k' ρ').symm
      have hb : Mask.incl body.writes (true :: body.writes.tail) := Mask.incl_cons (Mask.incl_refl _)
      simp only [TStmts.safe, TStmts.safeR, e, eb]
      congr 1
      exact forIn_proj _ _ ρ _ (fun y n n' e e' ρ' h hne => TStmts.safe_frame body hb _ _ (y, ρ') fun σ' h' =>
          have h2 := Agree.trans h (Agree.of_cons h')
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .forEntries _ _ a body rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have eb : ∀ k' ρ', body.safeR fs ss k' ρ' = body.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R body k' ρ').symm
      have hb : Mask.incl body.writes (true :: true :: body.writes.tail.tail) := Mask.incl_cons₂ (Mask.incl_refl _)
      simp only [TStmts.safe, TStmts.safeR, e, eb]
      congr 1
      exact forIn_proj _ _ ρ _ (fun (p : _ × Nat) n n' e e' ρ' h hne =>
          TStmts.safe_frame body hb _ _ (p.1, (p.2 : Int), ρ') fun σ' h' =>
            have h2 := Agree.trans h (Agree.of_cons₂ h')
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .forRange _ v body rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have eb : ∀ k' ρ', body.safeR fs ss k' ρ' = body.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R body k' ρ').symm
      have hb : Mask.incl body.writes (true :: body.writes.tail) := Mask.incl_cons (Mask.incl_refl _)
      simp only [TStmts.safe, TStmts.safeR, e, eb]
      exact forIn_proj _ _ ρ _ (fun j n n' e e' ρ' h hne => TStmts.safe_frame body hb _ _ (j, ρ') fun σ' h' =>
          have h2 := Agree.trans h (Agree.of_cons h')
          ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ ρ (Agree.refl _ _ ρ)
    | _, _, .whileLoop c body rest, k, ρ => by
      have e : rest.safeR fs ss k = rest.safe fs ss k := funext fun ρ' => (TStmts.safe_eq_R rest k ρ').symm
      have eb : ∀ k' ρ', body.safeR fs ss k' ρ' = body.safe fs ss k' ρ' := fun k' ρ' => (TStmts.safe_eq_R body k' ρ').symm
      simp only [TStmts.safe, TStmts.safeR, e, eb]
      rw [whileSafe_def, whileSafe_def]
      exact whileIn_proj _ _ ρ _ _ (fun n n' e e' ρ' h hne =>
          TStmts.safe_frame body (Mask.incl_refl _) _ _ ρ' fun σ' h' =>
            have h2 := Agree.trans h h'
            ⟨(hne _ h2).1, (hne _ h2).2, (hne _ h2).1⟩) _ _ _ ρ (Agree.refl _ _ ρ)

  theorem TArms.firstSafe_eq_R {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (k : K Γ Bool) (ρ : Γ.denote), arms.firstSafe fs ss k ρ = arms.firstSafeR fs ss k ρ
    | .nil, _, _ => rfl
    | .empty _ rest, k, ρ => TArms.firstSafe_eq_R rest k ρ
    | .wide _ body _, k, ρ => TStmts.safe_eq_R body k ρ
    | .narrow .., _, _ => rfl

  theorem TArms.safe_eq_R {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (k : K Γ Bool) (ρ : Γ.denote) {t : TagLit} {fds : Fields}
      (i : VIdx vs0 t fds) (y : fds.denote) (d : Bool), arms.safe fs ss k ρ i y d = arms.safeR fs ss k ρ i y d
    | .nil, _, _, _, _, _, _, _ => rfl
    | .empty l rest, k, ρ, t, _, i, y, d => by
      simp only [TArms.safe, TArms.safeR, TArms.firstSafe_eq_R rest k ρ]
      split
      · rfl
      · exact TArms.safe_eq_R rest k ρ i y _
    | .wide l body rest, k, ρ, t, _, i, y, d => by
      simp only [TArms.safe, TArms.safeR, TStmts.safe_eq_R body k ρ]
      split
      · rfl
      · exact TArms.safe_eq_R rest k ρ i y _
    | .narrow i' body rest, k, ρ, t, _, i, y, d => by
      rcases hp : i'.proj (i.inj y) with _ | y' <;> simp only [TArms.safe, TArms.safeR, hp]
      · exact TArms.safe_eq_R rest k ρ i y d
      · exact TStmts.safe_eq_R body _ _
end

/-- **The safety condition with states is the safety condition**: for every function body. -/
theorem TStmts.safeFn_eq_R {Γ : Ctx} {τ : Ty} (body : TStmts Φ Γ τ) : body.safeFn fs ss = body.safeRFn fs ss := by
  unfold TStmts.safeFn TStmts.safeRFn
  split
  · rfl
  · exact funext fun ρ => TStmts.safe_eq_R body _ ρ

end
end

end Ariadne

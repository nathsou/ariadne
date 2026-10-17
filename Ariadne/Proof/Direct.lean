import Ariadne.Typed.Direct
import Ariadne.Proof.Stmt
import Ariadne.Lib.Loop

/-!
# The direct-style denotation is the denotation

`TStmts.denoteFn_eq`: for every function body, `denoteDFn` (loops whose body is `direct` as folds) is
`denoteFn`. A generated file checks its readable definitions against `denoteDFn` by `rfl`, and this
theorem carries them to `denoteFn`, which the general theorem is about.

The proof rests on three facts about `denoteD`, each by induction on the syntax:
- naturality: a function `h` applied to the result can be pushed into the continuations (`denoteD_nat`);
- without a `return`, the result of one is irrelevant (`denoteD_noRet`);
- without a `break` of its own, the break continuation is (`denoteD_noBrk`).
A direct body's iteration `body (next, exit)` is then `next (body (id, id))`, so its loop is a fold
(`forIn_fold`).
-/

set_option linter.unusedSectionVars false

namespace Ariadne

theorem K.post_normal (k : K Γ A) (n : Γ.denote → A) (n' : Γ.denote → B) (h : A → B)
    (e : ∀ ρ, h (n ρ) = n' ρ) : ({ k with normal := n } : K Γ A).post h = { k.post h with normal := n' } := by
  simp only [Control.post, Control.mk.injEq, and_true]; funext ρ; exact e ρ

theorem K.post_normal_brk (k : K Γ A) (n : Γ.denote → A) (n' : Γ.denote → B) (h : A → B)
    (e : ∀ ρ, h (n ρ) = n' ρ) :
    ({ k with normal := n, brk := n } : K Γ A).post h = { k.post h with normal := n', brk := n' } := by
  simp only [Control.post, Control.mk.injEq, and_true]; constructor <;> funext ρ <;> exact e ρ

theorem forIn_nat {α σ A B : Type} (h : A → B) {step₁ : α → (σ → A) → (σ → A) → σ → A}
    {step₂ : α → (σ → B) → (σ → B) → σ → B} (hs : ∀ y n e s, h (step₁ y n e s) = step₂ y (h ∘ n) (h ∘ e) s)
    (exit₁ : σ → A) (exit₂ : σ → B) (he : ∀ s, h (exit₁ s) = exit₂ s) :
    ∀ (xs : List α) (s : σ), h (forIn xs step₁ exit₁ s) = forIn xs step₂ exit₂ s
  | [], s => he s
  | y :: ys, s => by
    show h (step₁ y (forIn ys step₁ exit₁) exit₁ s) = step₂ y (forIn ys step₂ exit₂) exit₂ s
    rw [hs]
    have e1 : (h ∘ forIn ys step₁ exit₁) = forIn ys step₂ exit₂ := funext (forIn_nat h hs exit₁ exit₂ he ys)
    have e2 : (h ∘ exit₁) = exit₂ := funext he
    rw [e1, e2]

theorem whileIn_nat {σ A B : Type} (h : A → B) (cond : σ → Bool) {step₁ : (σ → A) → (σ → A) → σ → A}
    {step₂ : (σ → B) → (σ → B) → σ → B} (hs : ∀ n e s, h (step₁ n e s) = step₂ (h ∘ n) (h ∘ e) s)
    (exit₁ stuck₁ : σ → A) (exit₂ stuck₂ : σ → B) (he : ∀ s, h (exit₁ s) = exit₂ s)
    (hst : ∀ s, h (stuck₁ s) = stuck₂ s) :
    ∀ (n : Nat) (s : σ), h (whileIn n cond step₁ exit₁ stuck₁ s) = whileIn n cond step₂ exit₂ stuck₂ s
  | 0, s => hst s
  | n + 1, s => by
    simp only [whileIn]
    split
    · rw [hs]
      have e1 : (h ∘ whileIn n cond step₁ exit₁ stuck₁) = whileIn n cond step₂ exit₂ stuck₂ :=
        funext (whileIn_nat h cond hs exit₁ stuck₁ exit₂ stuck₂ he hst n)
      have e2 : (h ∘ exit₁) = exit₂ := funext he
      rw [e1, e2]
    · exact he s

theorem whileDo_nat {σ A B : Type} (h : A → B) (cond : σ → Bool) {step₁ : (σ → A) → (σ → A) → σ → A}
    {step₂ : (σ → B) → (σ → B) → σ → B} (hs : ∀ n e s, h (step₁ n e s) = step₂ (h ∘ n) (h ∘ e) s)
    (exit₁ : σ → A) (exit₂ : σ → B) (he : ∀ s, h (exit₁ s) = exit₂ s) (s : σ) :
    h (whileDo cond step₁ exit₁ s) = whileDo cond step₂ exit₂ s := by
  rw [whileDo_def, whileDo_def]; exact whileIn_nat h cond hs exit₁ exit₁ exit₂ exit₂ he he _ s

/-- A loop whose iterations go on with `next` whatever their continuations: the iteration with `exit`
replaced by `next` (used when the body has no `break` of its own). -/
theorem forIn_congr_step {α σ R : Type} {step₁ step₂ : α → (σ → R) → (σ → R) → σ → R}
    (hs : ∀ y n e s, step₁ y n e s = step₂ y n e s) (exit : σ → R) (xs : List α) (s : σ) :
    forIn xs step₁ exit s = forIn xs step₂ exit s := by
  have : step₁ = step₂ := funext fun y => funext fun n => funext fun e => funext fun s => hs y n e s
  rw [this]

section
variable {Φ : Sigs} {fs : Φ.denote}

/-! ## Naturality -/

mutual
  theorem TStmts.denoteD_nat : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {A B : Type} (h : A → B)
      (r : τ.denote → A) (k : K Γ A) (ρ : Γ.denote), h (st.denoteD fs r k ρ) = st.denoteD fs (h ∘ r) (k.post h) ρ
    | _, _, .nil, _, _, _, _, _, _ => rfl
    | _, _, .brk _, _, _, _, _, _, _ => rfl
    | _, _, .cont _, _, _, _, _, _, _ => rfl
    | _, _, .ret _ _, _, _, _, _, _, _ => rfl
    | _, _, .retVoid _ _, _, _, _, _, _, _ => rfl
    | _, _, .const _ e rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .let_ _ e rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .assign _ e rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .stateSet _ _ _ _ _ rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .stateDelete _ _ _ _ rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .callVoid _ _ _ rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_nat rest h r _ _
    | _, _, .ite c yes no rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      have hk := K.post_normal k _ _ h (TStmts.denoteD_nat rest h r k)
      split
      · rw [TStmts.denoteD_nat yes h r, hk]
      · rw [TStmts.denoteD_nat no h r, hk]
    | _, _, .block body rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      rw [TStmts.denoteD_nat body h r, K.post_normal k _ _ h (TStmts.denoteD_nat rest h r k)]
    | _, _, .ifNull v _ yes no rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      have hk := K.post_normal k _ _ h (TStmts.denoteD_nat rest h r k)
      split
      · rw [TStmts.denoteD_nat yes h r, hk]
      · rw [TStmts.denoteD_nat no h r]
        show no.denoteD fs (h ∘ r) (K.map (v.widen some) (({ k with normal := rest.denoteD fs r k } : K _ _).post h)) _ = _
        rw [hk]
    | _, _, .ifNotNull v _ yes no rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      have hk := K.post_normal k _ _ h (TStmts.denoteD_nat rest h r k)
      split
      · rw [TStmts.denoteD_nat yes h r]
        show yes.denoteD fs (h ∘ r) (K.map (v.widen some) (({ k with normal := rest.denoteD fs r k } : K _ _).post h)) _ = _
        rw [hk]
      · rw [TStmts.denoteD_nat no h r, hk]
    | _, _, .ifNullExit v _ yes rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_nat yes h r k ρ
      · exact TStmts.denoteD_nat rest h r _ _
    | _, _, .switchG v _ arms rest, _, _, h, r, k, ρ => by
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, hu, Variants.elim_inj]
      rw [TArms.denoteD_nat arms h r _ ρ i y, K.post_normal_brk k _ _ h (TStmts.denoteD_nat rest h r k),
        TStmts.denoteD_nat rest h r k ρ]
    | _, _, .forOf _ a body rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_nat rest h r k _
      · exact forIn_nat h (fun y n e s => TStmts.denoteD_nat body h r _ (y, s)) _ _
          (TStmts.denoteD_nat rest h r k) _ _
    | _, _, .forEntries _ _ a body rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_nat rest h r k _
      · exact forIn_nat h (fun p n e s => TStmts.denoteD_nat body h r _ (p.1, (p.2 : Int), s)) _ _
          (TStmts.denoteD_nat rest h r k) _ _
    | _, _, .forRange _ v body rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_nat rest h r k _
      · exact forIn_nat h (fun j n e s => TStmts.denoteD_nat body h r _ (j, s)) _ _
          (TStmts.denoteD_nat rest h r k) _ _
    | _, _, .whileLoop c body rest, _, _, h, r, k, ρ => by
      simp only [TStmts.denoteD]
      exact whileDo_nat h _ (fun n e s => TStmts.denoteD_nat body h r _ s) _ _ (TStmts.denoteD_nat rest h r k) ρ

  theorem TArms.firstD_nat {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {A B : Type} (h : A → B) (r : τ.denote → A) (k : K Γ A) (ρ : Γ.denote),
      h (arms.firstD fs r k ρ) = arms.firstD fs (h ∘ r) (k.post h) ρ
    | .nil, _, _, _, _, _, _ => rfl
    | .empty _ rest, _, _, h, r, k, ρ => TArms.firstD_nat rest h r k ρ
    | .wide _ body _, _, _, h, r, k, ρ => TStmts.denoteD_nat body h r k ρ
    | .narrow .., _, _, _, _, _, _ => rfl

  theorem TArms.denoteD_nat {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {A B : Type} (h : A → B) (r : τ.denote → A) (k : K Γ A) (ρ : Γ.denote)
      {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d : A),
      h (arms.denoteD fs r k ρ i y d) = arms.denoteD fs (h ∘ r) (k.post h) ρ i y (h d)
    | .nil, _, _, _, _, _, _, _, _, _, _, _ => rfl
    | .empty l rest, _, _, h, r, k, ρ, t, _, i, y, d => by
      simp only [TArms.denoteD]
      split
      · exact TArms.firstD_nat rest h r k ρ
      · rw [TArms.denoteD_nat rest h r k ρ i y]
        congr 1
        split
        · exact TArms.firstD_nat rest h r k ρ
        · rfl
    | .wide l body rest, _, _, h, r, k, ρ, t, _, i, y, d => by
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_nat body h r k ρ
      · rw [TArms.denoteD_nat rest h r k ρ i y]
        congr 1
        split
        · exact TStmts.denoteD_nat body h r k ρ
        · rfl
    | .narrow i' body rest, _, _, h, r, k, ρ, t, _, i, y, d => by
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_nat body h r _ _
      · exact TArms.denoteD_nat rest h r k ρ i y d
end

/-! ## Irrelevance -/

mutual
  /-- Without a `return`, the result a `return` would give is irrelevant. -/
  theorem TStmts.denoteD_noRet : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {R : Type} (r r' : τ.denote → R)
      (k : K Γ R) (ρ : Γ.denote), st.noRet = true → st.denoteD fs r k ρ = st.denoteD fs r' k ρ
    | _, _, .nil, _, _, _, _, _, _ => rfl
    | _, _, .brk _, _, _, _, _, _, _ => rfl
    | _, _, .cont _, _, _, _, _, _, _ => rfl
    | _, _, .ret _ _, _, _, _, _, _, h => by simp [TStmts.noRet] at h
    | _, _, .retVoid _ _, _, _, _, _, _, h => by simp [TStmts.noRet] at h
    | _, _, .const _ e rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .let_ _ e rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .assign _ e rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .stateSet _ _ _ _ _ rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .stateDelete _ _ _ _ rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .callVoid _ _ _ rest, _, r, r', k, ρ, h => by
      simp only [TStmts.denoteD]; exact TStmts.denoteD_noRet rest r r' _ _ h
    | _, _, .ite c yes no rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noRet yes r r' _ ρ h.1.1
      · exact TStmts.denoteD_noRet no r r' _ ρ h.1.2
    | _, _, .block body rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      exact TStmts.denoteD_noRet body r r' _ ρ h.1
    | _, _, .ifNull v _ yes no rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noRet yes r r' _ ρ h.1.1
      · exact TStmts.denoteD_noRet no r r' _ _ h.1.2
    | _, _, .ifNotNull v _ yes no rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · exact TStmts.denoteD_noRet yes r r' _ _ h.1.1
      · exact TStmts.denoteD_noRet no r r' _ ρ h.1.2
    | _, _, .ifNullExit v _ yes rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      simp only [TStmts.denoteD]
      split
      · exact TStmts.denoteD_noRet yes r r' k ρ h.1
      · exact TStmts.denoteD_noRet rest r r' _ _ h.2
    | _, _, .switchG v _ arms rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denoteD, hu, Variants.elim_inj, e]
      exact TArms.denoteD_noRet arms r r' _ ρ i y _ h.1
    | _, _, .forOf _ a body rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · rfl
      · exact forIn_congr_step (fun y n x s => TStmts.denoteD_noRet body r r' _ (y, s) h.1) _ _ _
    | _, _, .forEntries _ _ a body rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · rfl
      · exact forIn_congr_step (fun (p : _ × Nat) n x s => TStmts.denoteD_noRet body r r' _ (p.1, (p.2 : Int), s) h.1) _ _ _
    | _, _, .forRange _ v body rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      simp only [TStmts.denoteD, e]
      split
      · rfl
      · exact forIn_congr_step (fun j n x s => TStmts.denoteD_noRet body r r' _ (j, s) h.1) _ _ _
    | _, _, .whileLoop c body rest, _, r, r', k, ρ, h => by
      simp only [TStmts.noRet, Bool.and_eq_true] at h
      have e : rest.denoteD fs r k = rest.denoteD fs r' k := funext fun ρ' => TStmts.denoteD_noRet rest r r' k ρ' h.2
      have eb : (fun next exit ρ' => body.denoteD fs r ⟨next, exit, next⟩ ρ') =
          (fun next exit ρ' => body.denoteD fs r' ⟨next, exit, next⟩ ρ') :=
        funext fun n => funext fun x => funext fun s => TStmts.denoteD_noRet body r r' _ s h.1
      simp only [TStmts.denoteD, e, eb]

  theorem TArms.firstD_noRet {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r r' : τ.denote → R) (k : K Γ R) (ρ : Γ.denote),
      arms.noRet = true → arms.firstD fs r k ρ = arms.firstD fs r' k ρ
    | .nil, _, _, _, _, _, _ => rfl
    | .empty _ rest, _, r, r', k, ρ, h => TArms.firstD_noRet rest r r' k ρ h
    | .wide _ body _, _, r, r', k, ρ, h => by
      simp only [TArms.noRet, Bool.and_eq_true] at h
      exact TStmts.denoteD_noRet body r r' k ρ h.1
    | .narrow .., _, _, _, _, _, _ => rfl

  theorem TArms.denoteD_noRet {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {R : Type} (r r' : τ.denote → R) (k : K Γ R) (ρ : Γ.denote)
      {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d : R),
      arms.noRet = true → arms.denoteD fs r k ρ i y d = arms.denoteD fs r' k ρ i y d
    | .nil, _, _, _, _, _, _, _, _, _, _, _ => rfl
    | .empty l rest, _, r, r', k, ρ, t, _, i, y, d, h => by
      simp only [TArms.noRet] at h
      simp only [TArms.denoteD, TArms.firstD_noRet rest r r' k ρ h]
      split
      · rfl
      · exact TArms.denoteD_noRet rest r r' k ρ i y _ h
    | .wide l body rest, _, r, r', k, ρ, t, _, i, y, d, h => by
      simp only [TArms.noRet, Bool.and_eq_true] at h
      simp only [TArms.denoteD, TStmts.denoteD_noRet body r r' k ρ h.1]
      split
      · rfl
      · exact TArms.denoteD_noRet rest r r' k ρ i y _ h.2
    | .narrow i' body rest, _, r, r', k, ρ, t, _, i, y, d, h => by
      simp only [TArms.noRet, Bool.and_eq_true] at h
      simp only [TArms.denoteD]
      split
      · exact TStmts.denoteD_noRet body r r' _ _ h.1
      · exact TArms.denoteD_noRet rest r r' k ρ i y d h.2
end

/-- Without a `break` of its own, the break continuation is irrelevant: two continuations that complete
and continue alike give the same result. -/
theorem TStmts.denoteD_noBrk : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {R : Type} (r : τ.denote → R)
    (k k' : K Γ R), k.normal = k'.normal → k.cont = k'.cont → st.noBrk = true → ∀ ρ, st.denoteD fs r k ρ = st.denoteD fs r k' ρ
  | _, _, .nil, _, _, _, _, hn, _, _, ρ => by simp only [TStmts.denoteD, hn]
  | _, _, .cont _, _, _, _, _, _, hc, _, ρ => by simp only [TStmts.denoteD, hc]
  | _, _, .brk _, _, _, _, _, _, _, h, _ => by simp [TStmts.noBrk] at h
  | _, _, .ret _ _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .retVoid _ _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .const _ e rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]
    exact TStmts.denoteD_noBrk rest r _ _ (by simp [hn]) (by simp [hc]) h _
  | _, _, .let_ _ e rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]
    exact TStmts.denoteD_noBrk rest r _ _ (by simp [hn]) (by simp [hc]) h _
  | _, _, .assign _ e rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]; exact TStmts.denoteD_noBrk rest r k k' hn hc h _
  | _, _, .stateSet _ _ _ _ _ rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]; exact TStmts.denoteD_noBrk rest r k k' hn hc h _
  | _, _, .stateDelete _ _ _ _ rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]; exact TStmts.denoteD_noBrk rest r k k' hn hc h _
  | _, _, .callVoid _ _ _ rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.denoteD]; exact TStmts.denoteD_noBrk rest r k k' hn hc h _
  | _, _, .ite c yes no rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk, Bool.and_eq_true] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h.2)
    simp only [TStmts.denoteD, e]
    split
    · exact TStmts.denoteD_noBrk yes r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
        rfl hc h.1.1 ρ
    · exact TStmts.denoteD_noBrk no r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
        rfl hc h.1.2 ρ
  | _, _, .block body rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk, Bool.and_eq_true] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h.2)
    simp only [TStmts.denoteD, e]
    exact TStmts.denoteD_noBrk body r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
      rfl hc h.1 ρ
  | _, _, .ifNull v _ yes no rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk, Bool.and_eq_true] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h.2)
    simp only [TStmts.denoteD, e]
    split
    · exact TStmts.denoteD_noBrk yes r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
        rfl hc h.1.1 ρ
    · exact TStmts.denoteD_noBrk no r (K.map (v.widen some) { k with normal := rest.denoteD fs r k' })
        (K.map (v.widen some) { k' with normal := rest.denoteD fs r k' }) rfl (by simp [hc]) h.1.2 _
  | _, _, .ifNotNull v _ yes no rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk, Bool.and_eq_true] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h.2)
    simp only [TStmts.denoteD, e]
    split
    · exact TStmts.denoteD_noBrk yes r (K.map (v.widen some) { k with normal := rest.denoteD fs r k' })
        (K.map (v.widen some) { k' with normal := rest.denoteD fs r k' }) rfl (by simp [hc]) h.1.1 _
    · exact TStmts.denoteD_noBrk no r { k with normal := rest.denoteD fs r k' } { k' with normal := rest.denoteD fs r k' }
        rfl hc h.1.2 ρ
  | _, _, .ifNullExit v _ yes rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk, Bool.and_eq_true] at h
    simp only [TStmts.denoteD]
    split
    · exact TStmts.denoteD_noBrk yes r k k' hn hc h.1 ρ
    · exact TStmts.denoteD_noBrk rest r _ _ (by simp [hn]) (by simp [hc]) h.2 _
  | _, _, .switchG v _ arms rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h)
    have ek : ({ k with normal := rest.denoteD fs r k, brk := rest.denoteD fs r k } : K _ _) =
        { k' with normal := rest.denoteD fs r k', brk := rest.denoteD fs r k' } := by
      rw [e]; cases k; cases k'; simp only at hc; subst hc; rfl
    simp only [TStmts.denoteD]
    rw [ek, e]
  | _, _, .forOf _ a body rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h)
    simp only [TStmts.denoteD, e]
  | _, _, .forEntries _ _ a body rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h)
    simp only [TStmts.denoteD, e]
  | _, _, .forRange _ v body rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h)
    simp only [TStmts.denoteD, e]
  | _, _, .whileLoop c body rest, _, r, k, k', hn, hc, h, ρ => by
    simp only [TStmts.noBrk] at h
    have e : rest.denoteD fs r k = rest.denoteD fs r k' := funext (TStmts.denoteD_noBrk rest r k k' hn hc h)
    simp only [TStmts.denoteD, e]

/-! ## The direct-style denotation is the denotation -/

/-- A direct body's iteration goes on with `next`, applied to what the body computes in direct style. -/
theorem TStmts.direct_step {Γ : Ctx} {σ τ : Ty} {x : String} (body : TStmts Φ ((x, σ) :: Γ) τ)
    (hd : body.direct = true) (next exit : Γ.denote → τ.denote) (σ' : Ctx.denote ((x, σ) :: Γ)) :
    body.denoteD fs id (K.map Prod.snd ⟨next, exit, next⟩) σ' =
      next (body.denoteD fs (fun _ => σ'.2) (K.map Prod.snd (K.all id)) σ') := by
  simp only [TStmts.direct, Bool.and_eq_true] at hd
  rw [TStmts.denoteD_nat body next (fun _ => σ'.2) (K.map Prod.snd (K.all id)) σ',
    TStmts.denoteD_noBrk body id (K.map Prod.snd ⟨next, exit, next⟩) (K.map Prod.snd ⟨next, next, next⟩) rfl rfl hd.2,
    TStmts.denoteD_noRet body id (next ∘ fun _ => σ'.2) _ σ' hd.1]
  rfl

/-- The same for a loop over entries, whose body binds the element and its index. -/
theorem TStmts.direct_step₂ {Γ : Ctx} {σ τ : Ty} {x i : String} (body : TStmts Φ ((x, σ) :: (i, .number) :: Γ) τ)
    (hd : body.direct = true) (next exit : Γ.denote → τ.denote) (σ' : Ctx.denote ((x, σ) :: (i, .number) :: Γ)) :
    body.denoteD fs id (K.map Prod.snd (K.map Prod.snd ⟨next, exit, next⟩)) σ' =
      next (body.denoteD fs (fun _ => σ'.2.2) (K.map Prod.snd (K.map Prod.snd (K.all id))) σ') := by
  simp only [TStmts.direct, Bool.and_eq_true] at hd
  rw [TStmts.denoteD_nat body next (fun _ => σ'.2.2) (K.map Prod.snd (K.map Prod.snd (K.all id))) σ',
    TStmts.denoteD_noBrk body id (K.map Prod.snd (K.map Prod.snd ⟨next, exit, next⟩))
      (K.map Prod.snd (K.map Prod.snd ⟨next, next, next⟩)) rfl rfl hd.2,
    TStmts.denoteD_noRet body id (next ∘ fun _ => σ'.2.2) _ σ' hd.1]
  rfl

mutual
  theorem TStmts.denote_eq_denoteD : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (k : K Γ τ.denote) (ρ : Γ.denote),
      st.denote fs k ρ = st.denoteD fs id k ρ
    | _, _, .nil, _, _ => rfl
    | _, _, .brk _, _, _ => rfl
    | _, _, .cont _, _, _ => rfl
    | _, _, .ret _ _, _, _ => rfl
    | _, _, .retVoid _ _, _, _ => rfl
    | _, _, .const _ e rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .let_ _ e rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .assign _ e rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .stateSet _ _ _ _ _ rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .stateDelete _ _ _ _ rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .callVoid _ _ _ rest, k, ρ => by
      simp only [TStmts.denote, TStmts.denoteD]; exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .ite c yes no rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      simp only [TStmts.denote, TStmts.denoteD, e]
      split
      · exact TStmts.denote_eq_denoteD yes _ ρ
      · exact TStmts.denote_eq_denoteD no _ ρ
    | _, _, .block body rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      simp only [TStmts.denote, TStmts.denoteD, e]
      exact TStmts.denote_eq_denoteD body _ ρ
    | _, _, .ifNull v _ yes no rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denote, TStmts.denoteD, e, hv]
      · exact TStmts.denote_eq_denoteD yes _ ρ
      · exact TStmts.denote_eq_denoteD no _ _
    | _, _, .ifNotNull v _ yes no rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denote, TStmts.denoteD, e, hv]
      · exact TStmts.denote_eq_denoteD no _ ρ
      · exact TStmts.denote_eq_denoteD yes _ _
    | _, _, .ifNullExit v _ yes rest, k, ρ => by
      rcases hv : v.get ρ with _ | y <;> simp only [TStmts.denote, TStmts.denoteD, hv]
      · exact TStmts.denote_eq_denoteD yes _ ρ
      · exact TStmts.denote_eq_denoteD rest _ _
    | _, _, .switchG v _ arms rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denote, TStmts.denoteD, hu, Variants.elim_inj, e]
      exact TArms.denote_eq_denoteD arms _ ρ i y _
    | _, _, .whileLoop c body rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      have eb : (fun next exit ρ' => body.denote fs ⟨next, exit, next⟩ ρ') =
          (fun next exit ρ' => body.denoteD fs id ⟨next, exit, next⟩ ρ') :=
        funext fun n => funext fun x => funext fun s => TStmts.denote_eq_denoteD body _ s
      simp only [TStmts.denote, TStmts.denoteD, e, eb]
    | _, _, .forOf _ a body rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      have eb := forIn_congr_step (fun y n x s => TStmts.denote_eq_denoteD body (K.map Prod.snd ⟨n, x, n⟩) (y, s))
      simp only [TStmts.denote, TStmts.denoteD, e, eb]
      split
      · rename_i hd
        rw [forIn_congr_step (fun y n x s => TStmts.direct_step body hd n x (y, s)), forIn_fold]
      · rfl
    | _, _, .forEntries _ _ a body rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      have eb := forIn_congr_step (fun (p : _ × Nat) n x s =>
        TStmts.denote_eq_denoteD body (K.map Prod.snd (K.map Prod.snd ⟨n, x, n⟩)) (p.1, (p.2 : Int), s))
      simp only [TStmts.denote, TStmts.denoteD, e, eb]
      split
      · rename_i hd
        rw [forIn_congr_step (fun (p : _ × Nat) n x s => TStmts.direct_step₂ body hd n x (p.1, (p.2 : Int), s)),
          forIn_fold]
      · rfl
    | _, _, .forRange _ v body rest, k, ρ => by
      have e : rest.denote fs k = rest.denoteD fs id k := funext (TStmts.denote_eq_denoteD rest k)
      have eb := forIn_congr_step (fun j n x s => TStmts.denote_eq_denoteD body (K.map Prod.snd ⟨n, x, n⟩) (j, s))
      simp only [TStmts.denote, TStmts.denoteD, e, eb]
      split
      · rename_i hd
        rw [forIn_congr_step (fun j n x s => TStmts.direct_step body hd n x (j, s)), forIn_fold]
      · rfl

  theorem TArms.first_eq_firstD {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (k : K Γ τ.denote) (ρ : Γ.denote), arms.first fs k ρ = arms.firstD fs id k ρ
    | .nil, _, _ => rfl
    | .empty _ rest, k, ρ => TArms.first_eq_firstD rest k ρ
    | .wide _ body _, k, ρ => TStmts.denote_eq_denoteD body k ρ
    | .narrow .., _, _ => rfl

  theorem TArms.denote_eq_denoteD {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (k : K Γ τ.denote) (ρ : Γ.denote) {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds)
      (y : fds.denote) (d : τ.denote), arms.denote fs k ρ i y d = arms.denoteD fs id k ρ i y d
    | .nil, _, _, _, _, _, _, _ => rfl
    | .empty l rest, k, ρ, t, _, i, y, d => by
      simp only [TArms.denote, TArms.denoteD, TArms.first_eq_firstD rest k ρ]
      split
      · rfl
      · exact TArms.denote_eq_denoteD rest k ρ i y _
    | .wide l body rest, k, ρ, t, _, i, y, d => by
      simp only [TArms.denote, TArms.denoteD, TStmts.denote_eq_denoteD body k ρ]
      split
      · rfl
      · exact TArms.denote_eq_denoteD rest k ρ i y _
    | .narrow i' body rest, k, ρ, t, _, i, y, d => by
      rcases hp : i'.proj (i.inj y) with _ | y' <;> simp only [TArms.denote, TArms.denoteD, hp]
      · exact TArms.denote_eq_denoteD rest k ρ i y d
      · exact TStmts.denote_eq_denoteD body _ _
end

/-- **The readable denotation is the denotation**: for every function body, `denoteDFn` (loops whose body
is `direct` as folds) is `denoteFn`, which the general theorem is about. -/
theorem TStmts.denoteFn_eq {Γ : Ctx} {τ : Ty} (body : TStmts Φ Γ τ) : body.denoteFn fs = body.denoteDFn fs :=
  funext fun ρ => TStmts.denote_eq_denoteD body _ ρ

end

end Ariadne

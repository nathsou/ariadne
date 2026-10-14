import V2.Proof.Stmt

/-!
# Trivially safe programs

Syntax with no operation that can leave what the model covers is safe, given that
the trivially safe functions it calls are. So a trivially safe function's safety
condition is `true` by definition (`TStmts.safeFn`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace V2

section
variable {Φ : Sigs} {fs : Φ.denote} {ss : Φ.safety}

theorem forIn_true {α σ : Type} {step : α → (σ → Bool) → (σ → Bool) → σ → Bool} {exit : σ → Bool}
    (hstep : ∀ y next exit ρ, (∀ ρ, next ρ = true) → (∀ ρ, exit ρ = true) → step y next exit ρ = true)
    (hexit : ∀ ρ, exit ρ = true) : ∀ (items : List α) ρ, forIn items step exit ρ = true
  | [], ρ => hexit ρ
  | y :: ys, ρ => hstep y _ exit ρ (forIn_true hstep hexit ys) hexit

/-- Continuations that are safe everywhere. -/
def K.True (k : K Γ Bool) : Prop := ∀ ρ, k.normal ρ = true ∧ k.brk ρ = true ∧ k.cont ρ = true

mutual
  theorem TStmts.safe_of_trivial : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (ks : K Γ Bool) (ρ : Γ.denote),
      ks.True → st.trivial = true → st.safe fs ss ks ρ = true
    | _, _, .nil, _, ρ, hk, _ => (hk ρ).1
    | _, _, .brk _, _, ρ, hk, _ => (hk ρ).2.1
    | _, _, .cont _, _, ρ, hk, _ => (hk ρ).2.2
    | _, _, .let_ _ e rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1, Bool.true_or, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ (fun ρ' => hk ρ'.2) h.2
    | _, _, .assign _ e rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1, Bool.true_or, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ hk h.2
    | _, _, .forOf _ a body rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1.1, Bool.true_or, Bool.true_and]
      exact forIn_true (fun y next exit ρ' hn hx => TStmts.safe_of_trivial body _ _
        (fun ρ'' => ⟨hn _, hx _, hn _⟩) h.1.2) (fun ρ' => TStmts.safe_of_trivial rest ks ρ' hk h.2) _ _
    | _, _, .forEntries _ _ a body rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1.1, Bool.true_or, Bool.true_and]
      exact forIn_true (fun y next exit ρ' hn hx => TStmts.safe_of_trivial body _ _
        (fun ρ'' => ⟨hn _, hx _, hn _⟩) h.1.2) (fun ρ' => TStmts.safe_of_trivial rest ks ρ' hk h.2) _ _
    | _, _, .const _ e rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1, Bool.true_or, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ (fun ρ' => hk ρ'.2) h.2
    | _, _, .ret e _, _, ρ, _, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp [TStmts.safe, h.1]
    | _, _, .retVoid _ _, _, _, _, _ => rfl
    | _, _, .stateSet _ _ _ key e rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, andT, h.1.1, h.1.2, ite_true, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ hk h.2
    | _, _, .stateDelete _ _ _ key rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, h.1, Bool.true_or, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ hk h.2
    | _, _, .callVoid _ _ args rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, andT, h.1.1, h.1.2, ite_true, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ hk h.2
    | _, _, .ite c yes no rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      have hk' : K.True { ks with normal := rest.safe fs ss ks } :=
        fun ρ' => ⟨TStmts.safe_of_trivial rest ks ρ' hk h.2, (hk ρ').2⟩
      simp only [TStmts.safe, h.1.1.1, Bool.true_or, Bool.true_and]
      split
      · exact TStmts.safe_of_trivial yes _ ρ hk' h.1.1.2
      · exact TStmts.safe_of_trivial no _ ρ hk' h.1.2
    | _, _, .block body rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      exact TStmts.safe_of_trivial body _ ρ (fun ρ' => ⟨TStmts.safe_of_trivial rest ks ρ' hk h.2, (hk ρ').2⟩) h.1
    | _, _, .ifNull v _ yes no rest, ks, ρ, hk, h | _, _, .ifNotNull v _ yes no rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      have hk' : K.True { ks with normal := rest.safe fs ss ks } :=
        fun ρ' => ⟨TStmts.safe_of_trivial rest ks ρ' hk h.2, (hk ρ').2⟩
      simp only [TStmts.safe]
      split
      · first
        | exact TStmts.safe_of_trivial yes _ ρ hk' h.1.1
        | exact TStmts.safe_of_trivial no _ _ (fun ρ' => hk' _) h.1.2
        | exact TStmts.safe_of_trivial yes _ _ (fun ρ' => hk' _) h.1.1
        | exact TStmts.safe_of_trivial no _ ρ hk' h.1.2
      · first
        | exact TStmts.safe_of_trivial no _ _ (fun ρ' => hk' _) h.1.2
        | exact TStmts.safe_of_trivial yes _ ρ hk' h.1.1
        | exact TStmts.safe_of_trivial yes _ _ (fun ρ' => hk' _) h.1.1
        | exact TStmts.safe_of_trivial no _ ρ hk' h.1.2
    | _, _, .ifNullExit v _ yes rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe]
      split
      · exact TStmts.safe_of_trivial yes ks ρ hk h.1
      · exact TStmts.safe_of_trivial rest _ _ (fun ρ' => hk _) h.2
    | _, _, .switchG v _ arms rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      have hr := fun ρ' => TStmts.safe_of_trivial rest ks ρ' hk h.2
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.safe, hu, Variants.elim_inj]
      exact TArms.safe_of_trivial arms _ ρ i y _ (fun ρ' => ⟨hr ρ', hr ρ', (hk ρ').2.2⟩) h.1 (hr ρ)
  theorem TArms.firstSafe_of_trivial {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} : ∀ (arms : TArms Φ Γ τ v) (ks : K Γ Bool) (ρ : Γ.denote), ks.True →
      arms.trivial = true → arms.firstSafe fs ss ks ρ = true
    | .nil, _, ρ, hk, _ => (hk ρ).1
    | .empty _ rest, ks, ρ, hk, h => TArms.firstSafe_of_trivial rest ks ρ hk h
    | .wide _ body _, ks, ρ, hk, h => by
      simp only [TArms.trivial, Bool.and_eq_true] at h
      exact TStmts.safe_of_trivial body ks ρ hk h.1
    | .narrow .., _, ρ, hk, _ => (hk ρ).1

  theorem TArms.safe_of_trivial {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} : ∀ (arms : TArms Φ Γ τ v) (ks : K Γ Bool) (ρ : Γ.denote) {t : TagLit}
      {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (dS : Bool), ks.True → arms.trivial = true → dS = true →
      arms.safe fs ss ks ρ i y dS = true
    | .nil, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, ks, ρ, _, _, i, y, dS, hk, h, hd => by
      simp only [TArms.trivial] at h
      simp only [TArms.safe]
      split
      · exact TArms.firstSafe_of_trivial rest ks ρ hk h
      · refine TArms.safe_of_trivial rest ks ρ i y _ hk h ?_
        split
        · exact TArms.firstSafe_of_trivial rest ks ρ hk h
        · exact hd
    | .wide l body rest, ks, ρ, _, _, i, y, dS, hk, h, hd => by
      simp only [TArms.trivial, Bool.and_eq_true] at h
      simp only [TArms.safe]
      split
      · exact TStmts.safe_of_trivial body ks ρ hk h.1
      · refine TArms.safe_of_trivial rest ks ρ i y _ hk h.2 ?_
        split
        · exact TStmts.safe_of_trivial body ks ρ hk h.1
        · exact hd
    | .narrow i' body rest, ks, ρ, _, _, i, y, dS, hk, h, hd => by
      simp only [TArms.trivial, Bool.and_eq_true] at h
      simp only [TArms.safe]
      split
      · exact TStmts.safe_of_trivial body _ _ (fun ρ' => hk _) h.1
      · exact TArms.safe_of_trivial rest ks ρ i y dS hk h.2 hd

end

end

theorem TProgram.safeSigs : ∀ {Φ : Sigs} (P : TProgram Φ), P.bodiesOk = true → SafeSigs P.safety
  | _, .nil, _ => fun v => nomatch v
  | _, .cons s body rest, h => by
    simp only [TProgram.bodiesOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    have ih : SafeSigs rest.safety := rest.safeSigs h.2
    intro v xs ht
    cases v with
    | there v => exact ih v xs ht
    | here =>
      show body.safeFn rest.denote rest.safety xs = true
      unfold TStmts.safeFn
      rcases h.1.2 with h' | h'
      · simp [h'] at ht
      · simp [h']

end V2

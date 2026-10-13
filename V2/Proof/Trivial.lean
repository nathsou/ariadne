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
    | _, _, .switchU v _ cases rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      have hr := fun ρ' => TStmts.safe_of_trivial rest ks ρ' hk h.2
      exact TCases.safe_of_trivial cases _ ρ id _ (fun ρ' => ⟨hr ρ', hr ρ', (hk ρ').2.2⟩) h.1

  theorem TCases.safe_of_trivial {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} : ∀ {vs : Variants} (cases : TCases Φ Γ τ v vs) (ks : K Γ Bool) (ρ : Γ.denote)
      (inj : vs.denote → vs0.denote) (u : vs.denote), ks.True → cases.trivial = true →
      cases.safe fs ss ks ρ inj u = true
    | _, .one body, ks, ρ, inj, u, hk, h => TStmts.safe_of_trivial body _ _ (fun ρ' => hk _) h
    | _, .cons body more, ks, ρ, inj, u, hk, h => by
      simp only [TCases.trivial, Bool.and_eq_true] at h
      cases u with
      | inl y => exact TStmts.safe_of_trivial body _ _ (fun ρ' => hk _) h.1
      | inr w => exact TCases.safe_of_trivial more ks ρ _ w hk h.2
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

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

/-- The safety conditions of trivially safe functions hold everywhere. -/
def SafeSigs {Φ : Sigs} (ss : Φ.safety) : Prop :=
  ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote), s.trivial = true → v.safe ss xs = true

section
variable {Φ : Sigs} {fs : Φ.denote} {ss : Φ.safety} (hss : SafeSigs ss)
include hss

mutual
  theorem TExpr.safe_of_trivial : ∀ {Γ : Ctx} {τ : Ty} (e : TExpr Φ Γ τ) (ρ : Γ.denote), e.trivial = true →
      e.safe fs ss ρ = true
    | _, _, .bool _, _, _ | _, _, .int _, _, _ | _, _, .str _, _, _ | _, _, .tagLit _, _, _
    | _, _, .litIn .., _, _ | _, _, .undef .., _, _ | _, _, .null .., _, _ | _, _, .var _, _, _ => rfl
    | _, _, .widen _ e, ρ, h | _, _, .not e, ρ, h | _, _, .neg e, ρ, h | _, _, .isNull _ e, ρ, h
    | _, _, .notNull _ e, ρ, h | _, _, .field e _ _, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TExpr.safe_of_trivial e ρ h]
    | _, _, .add a b, ρ, h | _, _, .sub a b, ρ, h | _, _, .mul a b, ρ, h | _, _, .concat a b, ρ, h
    | _, _, .eq _ a b, ρ, h | _, _, .ne _ a b, ρ, h | _, _, .lt a b, ρ, h | _, _, .le a b, ρ, h
    | _, _, .gt a b, ρ, h | _, _, .ge a b, ρ, h | _, _, .slt a b, ρ, h | _, _, .sle a b, ρ, h
    | _, _, .sgt a b, ρ, h | _, _, .sge a b, ρ, h | _, _, .and a b, ρ, h | _, _, .or a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, TExpr.safe_of_trivial a ρ h.1, TExpr.safe_of_trivial b ρ h.2]
    | _, _, .coalesce _ a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp only [TExpr.safe, TExpr.safe_of_trivial a ρ h.1, TExpr.safe_of_trivial b ρ h.2, Bool.true_and]
      split <;> rfl
    | _, _, .cond c a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, TExpr.safe_of_trivial c ρ h.1.1, TExpr.safe_of_trivial a ρ h.1.2,
        TExpr.safe_of_trivial b ρ h.2]
    | _, _, .condNull v _ a b, ρ, h | _, _, .condNotNull v _ a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp only [TExpr.safe]
      split
      · exact TExpr.safe_of_trivial _ _ (by first | exact h.1 | exact h.2)
      · exact TExpr.safe_of_trivial _ _ (by first | exact h.1 | exact h.2)
    | _, _, .call fn _ args, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, TArgs.safe_of_trivial args ρ h.2, hss fn _ h.1]
    | _, _, .record es _ _, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TEntries.safe_of_trivial es ρ h]
    | _, _, .update r es _ _, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, TExpr.safe_of_trivial r ρ h.1, TEntries.safe_of_trivial es ρ h.2]

  theorem TArgs.safe_of_trivial : ∀ {Γ ps : Ctx} (args : TArgs Φ Γ ps) (ρ : Γ.denote), args.trivial = true →
      args.safe fs ss ρ = true
    | _, _, .nil, _, _ | _, _, .omitted _, _, _ => rfl
    | _, _, .cons e rest, ρ, h => by
      simp only [TArgs.trivial, Bool.and_eq_true] at h
      simp [TArgs.safe, TExpr.safe_of_trivial e ρ h.1, TArgs.safe_of_trivial rest ρ h.2]

  theorem TEntries.safe_of_trivial : ∀ {Γ : Ctx} {src : Fields} (es : TEntries Φ Γ src) (ρ : Γ.denote),
      es.trivial = true → es.safe fs ss ρ = true
    | _, _, .nil, _, _ => rfl
    | _, _, .cons _ e rest, ρ, h => by
      simp only [TEntries.trivial, Bool.and_eq_true] at h
      simp [TEntries.safe, TExpr.safe_of_trivial e ρ h.1, TEntries.safe_of_trivial rest ρ h.2]
end

/-- Continuations that are safe everywhere. -/
def K.True (k : K Γ Bool) : Prop := ∀ ρ, k.normal ρ = true ∧ k.brk ρ = true ∧ k.cont ρ = true

mutual
  theorem TStmts.safe_of_trivial : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (ks : K Γ Bool) (ρ : Γ.denote),
      ks.True → st.trivial = true → st.safe fs ss ks ρ = true
    | _, _, .nil, _, ρ, hk, _ => (hk ρ).1
    | _, _, .brk _, _, ρ, hk, _ => (hk ρ).2.1
    | _, _, .const _ e rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      simp only [TStmts.safe, TExpr.safe_of_trivial hss e ρ h.1, Bool.true_and]
      exact TStmts.safe_of_trivial rest _ _ (fun ρ' => hk ρ'.2) h.2
    | _, _, .ret e _, _, ρ, _, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      exact TExpr.safe_of_trivial hss e ρ h.1
    | _, _, .ite c yes no rest, ks, ρ, hk, h => by
      simp only [TStmts.trivial, Bool.and_eq_true] at h
      have hk' : K.True { ks with normal := rest.safe fs ss ks } :=
        fun ρ' => ⟨TStmts.safe_of_trivial rest ks ρ' hk h.2, (hk ρ').2⟩
      simp only [TStmts.safe, TExpr.safe_of_trivial hss c ρ h.1.1.1, Bool.true_and]
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

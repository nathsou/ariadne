import V2.Proof.State
import V2.Eqns.Safe
import V2.Eqns.Trivial

/-!
# Trivially safe expressions

A trivially safe expression's safety condition is `true` by definition: its
parent leaves it out (`andT`), and every node of it is trivially safe.
-/

set_option linter.unusedSimpArgs false

namespace V2

theorem andT_elim {ta a tb b : Bool} (h : andT ta a tb b = true) (ha : ta = true → a = true)
    (hb : tb = true → b = true) : a = true ∧ b = true := by
  cases ta <;> cases tb <;> simp_all [andT]

theorem orT_elim {t a : Bool} (h : (t || a) = true) (ha : t = true → a = true) : a = true := by
  cases t <;> simp_all

theorem anySafe_true {p s : α → Bool} (h : ∀ x, s x = true) : ∀ xs, anySafe p s xs = true
  | [] => rfl
  | x :: xs => by simp [anySafe, h x, anySafe_true h xs]

theorem allSafe_true {p s : α → Bool} (h : ∀ x, s x = true) : ∀ xs, allSafe p s xs = true
  | [] => rfl
  | x :: xs => by simp [allSafe, h x, allSafe_true h xs]

theorem Op.guard_total (op : Op σ τ) {s : Bool} {x y : σ.denote} (h : op.total = true) : op.guard s x y = s := by
  cases op <;> simp_all [Op.total, Op.guard]

/-- The safety conditions of trivially safe functions hold everywhere. -/
def SafeSigs {Φ : Sigs} (ss : Φ.safety) : Prop :=
  ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote), s.trivial = true → v.safe ss xs = true

section
variable {Φ : Sigs} {fs : Φ.denote} {ss : Φ.safety}

mutual
  theorem TExpr.safe_of_trivial : ∀ {Γ : Ctx} {τ : Ty} (e : TExpr Φ Γ τ) (ρ : Γ.denote), e.trivial = true →
      e.safe fs ss ρ = true
    | _, _, .bool _, _, _ | _, _, .int _, _, _ | _, _, .str _, _, _ | _, _, .tagLit _, _, _
    | _, _, .litIn .., _, _ | _, _, .undef .., _, _ | _, _, .null .., _, _ | _, _, .var _, _, _
    | _, _, .num _, _, _ | _, _, .negNum .., _, _ => rfl
    | _, _, .widen _ e, ρ, h | _, _, .not e, ρ, h | _, _, .neg e, ρ, h | _, _, .isNull _ e, ρ, h
    | _, _, .notNull _ e, ρ, h | _, _, .field e _ _, ρ, h | _, _, .length e, ρ, h | _, _, .slength e, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TExpr.safe_of_trivial e ρ h]
    | _, _, .record es _ _, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TEntries.safe_of_trivial es ρ h]
    | _, _, .array es, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TElems.safe_of_trivial es ρ h]
    | _, _, .nneg _, _, h | _, _, .sorted .., _, h => by simp [TExpr.trivial] at h
    | _, _, .bin op a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, op.guard_total h.1.1, andT, TExpr.safe_of_trivial a ρ h.1.2, TExpr.safe_of_trivial b ρ h.2]
    | _, _, .and a b, ρ, h | _, _, .or a b, ρ, h
    | _, _, .coalesce _ a b, ρ, h | _, _, .index a b, ρ, h | _, _, .includes _ a b, ρ, h
    | _, _, .any a b, ρ, h | _, _, .all a b, ρ, h | _, _, .find a b, ρ, h | _, _, .filter a b, ρ, h
    | _, _, .map a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, andT, h.1, h.2]
    | _, _, .cond c a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, andT, h.1.1, h.1.2, h.2]
    | _, _, .condNull v _ a b, ρ, h | _, _, .condNotNull v _ a b, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp only [TExpr.safe]
      split <;> simp [h.1, h.2]
    | _, _, .call fn _ args, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, andT, h.1, h.2]
    | _, _, .update r es _ _, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, andT, h.1, h.2]
    | _, _, .newMap _, _, _ | _, _, .stateSize _ _, _, _ => rfl
    | _, _, .stateGet _ _ _ k, ρ, h | _, _, .stateHas _ _ k, ρ, h => by
      simp only [TExpr.trivial] at h; simp [TExpr.safe, TExpr.safe_of_trivial k ρ h]
    | _, _, .callThis fn v args, ρ, h => by
      simp only [TExpr.trivial, Bool.and_eq_true] at h
      simp [TExpr.safe, andT, h.1, h.2]

  theorem TArgs.safe_of_trivial : ∀ {Γ ps : Ctx} (args : TArgs Φ Γ ps) (ρ : Γ.denote), args.trivial = true →
      args.safe fs ss ρ = true
    | _, _, .nil, _, _ | _, _, .omitted _, _, _ => rfl
    | _, _, .cons e rest, ρ, h => by
      simp only [TArgs.trivial, Bool.and_eq_true] at h
      simp [TArgs.safe, andT, h.1, h.2]

  theorem TEntries.safe_of_trivial : ∀ {Γ : Ctx} {src : Fields} (es : TEntries Φ Γ src) (ρ : Γ.denote),
      es.trivial = true → es.safe fs ss ρ = true
    | _, _, .nil, _, _ => rfl
    | _, _, .cons _ e rest, ρ, h => by
      simp only [TEntries.trivial, Bool.and_eq_true] at h
      simp [TEntries.safe, andT, h.1, h.2]

  theorem TElems.safe_of_trivial : ∀ {Γ : Ctx} {τ : Ty} (es : TElems Φ Γ τ) (ρ : Γ.denote),
      es.trivial = true → es.safe fs ss ρ = true
    | _, _, .nil, _, _ => rfl
    | _, _, .cons e rest, ρ, h | _, _, .spread e rest, ρ, h => by
      simp only [TElems.trivial, Bool.and_eq_true] at h
      simp [TElems.safe, andT, h.1, h.2]
    | _, _, .spreadKeys _ _ rest, ρ, h | _, _, .spreadValues _ _ rest, ρ, h => by
      simp only [TElems.trivial] at h; simp [TElems.safe, TElems.safe_of_trivial rest ρ h]
end

theorem TFn.safe_of_trivial (hss : SafeSigs ss) : ∀ {Γ : Ctx} {τ σ : Ty} (p : TFn Φ Γ τ σ) (ρ : Γ.denote)
    (y : τ.denote), p.trivial = true → p.safe fs ss ρ y = true
  | _, _, _, .arrow _ body, ρ, y, h => body.safe_of_trivial (y, ρ) h
  | _, _, _, .const body, ρ, _, h => body.safe_of_trivial ρ h
  | _, _, _, .ref fn _, _, y, h => hss fn (y, ()) h

theorem TCmp.safe_of_trivial (hss : SafeSigs ss) : ∀ {Γ : Ctx} {τ : Ty} (c : TCmp Φ Γ τ) (ρ : Γ.denote)
    (y z : τ.denote), c.trivial = true → c.safe fs ss ρ y z = true
  | _, _, .arrow _ _ body, ρ, y, z, h => body.safe_of_trivial (y, z, ρ) h
  | _, _, .ref fn _, _, y, z, h => hss fn (y, z, ()) h

/-- A subterm's safety, as its parent consults it. -/
theorem TExpr.ok {Γ : Ctx} {τ : Ty} {e : TExpr Φ Γ τ} {ρ : Γ.denote} (h : (e.trivial || e.safe fs ss ρ) = true) :
    e.safe fs ss ρ = true :=
  orT_elim h (e.safe_of_trivial ρ)

end

end V2

import Ariadne.Typed.Named
import Ariadne.Proof.Idiom

/-!
# The denotation over named types is the denotation

`TStmts.denoteFn_eq_S`: for every function body, `denoteFn` on the denotation's values is `denoteRSFn` (over
a program's structures and inductives) on the converted values, converted back. A generated file checks its
readable definitions against `denoteRSFn` by `rfl`, and this theorem carries them to the general theorem.

The proof is a logical relation: every denotation commutes with the conversion `Ty.conv`, by induction on
the syntax, given only the isomorphism laws of the program's types (`Isos`).
-/

set_option linter.unusedSectionVars false

namespace Ariadne

section
variable {N : Names} (I : Isos N)

/-! ## The isomorphisms, generically -/

theorem recViewAux_recMkAux (fs : Fields) : ∀ (o : Option (Fin N.recs.length))
    (h h' : ∀ i, o = some i → N.recs[i].1 = fs) (x : fs.den N),
    recViewAux N I fs o h (recMkAux N I fs o h' x) = x
  | some i, h, h', x => by simp only [recViewAux, recMkAux, I.view_make, cast_cast, cast_eq]
  | none, _, _, _ => rfl

theorem recMkAux_recViewAux (fs : Fields) : ∀ (o : Option (Fin N.recs.length))
    (h h' : ∀ i, o = some i → N.recs[i].1 = fs) (r : recTy N fs o),
    recMkAux N I fs o h (recViewAux N I fs o h' r) = r
  | some i, h, h', r => by simp only [recViewAux, recMkAux, cast_cast, cast_eq, I.make_view]
  | none, _, _, _ => rfl

theorem recView_recMk (fs : Fields) (x : fs.den N) : recView N I fs (recMk N I fs x) = x :=
  recViewAux_recMkAux I fs _ _ _ x

theorem recMk_recView (fs : Fields) (r : recTy N fs (N.idx fs)) : recMk N I fs (recView N I fs r) = r :=
  recMkAux_recViewAux I fs _ _ _ r

theorem Variants.elimS_injS {R : Type} : ∀ {vs : Variants} {t : TagLit} {fs : Fields} (i : VIdx vs t fs)
    (y : fs.den N) (k : ∀ {t fs}, VIdx vs t fs → fs.den N → R), Variants.elimS N vs (VIdx.injS N i y) k = k i y
  | _, _, _, .one, _, _ => rfl
  | _, _, _, .head, _, _ => rfl
  | _, _, _, .there i, y, k => Variants.elimS_injS i y (fun j z => k (.there j) z)

theorem Variants.elimS_nat {R R' : Type} (f : R → R') : ∀ (vs : Variants) (x : vs.den N)
    (k : ∀ {t fs}, VIdx vs t fs → fs.den N → R), f (Variants.elimS N vs x k) = Variants.elimS N vs x (fun j y => f (k j y))
  | .one _ _, _, _ => rfl
  | .cons _ _ _, .inl _, _ => rfl
  | .cons _ _ rest, .inr w, k => Variants.elimS_nat f rest w (fun j y => k (.there j) y)

/-- Taking a union value apart into its variant and putting it back. -/
theorem Variants.elimS_self : ∀ (vs : Variants) (x : vs.den N), Variants.elimS N vs x (fun j y => VIdx.injS N j y) = x
  | .one _ _, _ => rfl
  | .cons _ _ _, .inl _ => rfl
  | .cons _ _ rest, .inr w => by
    show Variants.elimS N rest w (fun j y => Sum.inr (VIdx.injS N j y)) = Sum.inr w
    rw [← Variants.elimS_nat Sum.inr rest w, Variants.elimS_self rest w]

theorem unionElimAux_eq (vs : Variants) {R : Type} : ∀ (o : Option (Fin N.unions.length))
    (h h' : ∀ i, o = some i → N.unions[i].1 = vs) (u : unionTy N vs o) (k : ∀ {t fs}, VIdx vs t fs → fs.den N → R),
    unionElimAux N I vs o h u k = Variants.elimS N vs (unionElimAux N I vs o h' u fun j y => VIdx.injS N j y) k
  | some i, h, h', u, k => by
    have e := h i rfl
    simp only [unionElimAux]
    rw [← I.umake_uelim i u, I.uelim_umake, I.uelim_umake]
    generalize I.uelim i u (fun j y => VIdx.injS N j y) = x
    subst e
    simp only [cast_eq]
    exact (congrArg (fun z => Variants.elimS N _ z k) (Variants.elimS_self _ x)).symm
  | none, _, _, u, k => by
    simp only [unionElimAux]
    rw [Variants.elimS_self vs u]

theorem unionElim_eq (vs : Variants) {R : Type} (u : unionTy N vs (N.uidx vs)) (k : ∀ {t fs}, VIdx vs t fs → fs.den N → R) :
    unionElim N I vs u k = Variants.elimS N vs (unionView N I vs u) k :=
  unionElimAux_eq I vs _ _ _ u k

theorem unionElimAux_mkAux (vs : Variants) : ∀ (o : Option (Fin N.unions.length))
    (h h' : ∀ i, o = some i → N.unions[i].1 = vs) (x : vs.den N),
    unionElimAux N I vs o h (unionMkAux N I vs o h' x) (fun j y => VIdx.injS N j y) = x
  | some i, h, h', x => by
    have e := h i rfl
    simp only [unionElimAux, unionMkAux, I.uelim_umake]
    subst e
    simp only [cast_eq]
    exact Variants.elimS_self _ x
  | none, _, _, x => Variants.elimS_self vs x

theorem unionView_unionMk (vs : Variants) (x : vs.den N) : unionView N I vs (unionMk N I vs x) = x :=
  unionElimAux_mkAux I vs _ _ _ x

theorem unionMkAux_elimAux (vs : Variants) : ∀ (o : Option (Fin N.unions.length))
    (h h' : ∀ i, o = some i → N.unions[i].1 = vs) (u : unionTy N vs o),
    unionMkAux N I vs o h (unionElimAux N I vs o h' u fun j y => VIdx.injS N j y) = u
  | some i, h, h', u => by
    have e := h i rfl
    simp only [unionElimAux, unionMkAux]
    conv => rhs; rw [← I.umake_uelim i u]
    congr 1
    subst e
    simp only [cast_eq]
  | none, _, _, u => Variants.elimS_self vs u

theorem unionMk_unionView (vs : Variants) (u : unionTy N vs (N.uidx vs)) : unionMk N I vs (unionView N I vs u) = u :=
  unionMkAux_elimAux I vs _ _ _ u

end

/-! ## Conversions commute with the operations -/

section
variable {N : Names} (I : Isos N)

theorem Fields.conv_cons {f : String} {τ : Ty} {rest : Fields} (x : Fields.den N (.cons f τ rest)) :
    Fields.conv N I (.cons f τ rest) x = (Ty.conv N I τ x.1, Fields.conv N I rest x.2) := by
  obtain ⟨a, b⟩ := x; rfl

theorem Ty.conv_record (fs : Fields) (r : Ty.den N (.record fs)) :
    Ty.conv N I (.record fs) r = Fields.conv N I fs (recView N I fs r) := rfl

theorem Ty.conv_union (k : String) (vs : Variants) (u : Ty.den N (.union k vs)) :
    Ty.conv N I (.union k vs) u = Variants.conv N I vs (unionView N I vs u) := rfl

theorem Ty.conv_recMk (fs : Fields) (x : fs.den N) :
    Ty.conv N I (.record fs) (recMk N I fs x) = Fields.conv N I fs x := by
  rw [Ty.conv_record, recView_recMk]

theorem Ty.conv_unionMk (k : String) (vs : Variants) (x : vs.den N) :
    Ty.conv N I (.union k vs) (unionMk N I vs x) = Variants.conv N I vs x := by
  rw [Ty.conv_union, unionView_unionMk]

theorem Variants.conv_injS : ∀ {vs : Variants} {t : TagLit} {fs : Fields} (i : VIdx vs t fs) (y : fs.den N),
    Variants.conv N I vs (VIdx.injS N i y) = i.inj (Fields.conv N I fs y)
  | _, _, _, .one, _ => rfl
  | _, _, _, .head, _ => rfl
  | _, _, _, .there i, y => by
    show Sum.inr _ = Sum.inr _
    rw [Variants.conv_injS i y]

theorem Variants.elim_conv {R : Type} : ∀ (vs : Variants) (x : vs.den N) (k : ∀ {t fs}, VIdx vs t fs → fs.denote → R),
    Variants.elim vs (Variants.conv N I vs x) k = Variants.elimS N vs x (fun i y => k i (Fields.conv N I _ y))
  | .one _ _, _, _ => rfl
  | .cons _ _ _, .inl _, _ => rfl
  | .cons _ _ rest, .inr w, k => Variants.elim_conv rest w (fun i y => k (.there i) y)

theorem VIdx.proj_conv : ∀ {vs : Variants} {t : TagLit} {fs : Fields} (i : VIdx vs t fs) (u : vs.den N),
    i.proj (Variants.conv N I vs u) = (VIdx.projS N i u).map (Fields.conv N I fs)
  | _, _, _, .one, _ => rfl
  | _, _, _, .head, .inl _ => rfl
  | _, _, _, .head, .inr _ => rfl
  | _, _, _, .there _, .inl _ => rfl
  | _, _, _, .there i, .inr w => VIdx.proj_conv i w

theorem FIdx.conv_getS : ∀ {fs : Fields} {f : String} {τ : Ty} (i : FIdx fs f τ) (x : fs.den N),
    Ty.conv N I τ (FIdx.getS N i x) = i.get (Fields.conv N I fs x)
  | .cons .., _, _, .here, (_, _) => rfl
  | .cons .., _, _, .there i, (_, xs) => FIdx.conv_getS i xs

theorem FIdx.conv_setS : ∀ {fs : Fields} {f : String} {τ : Ty} (i : FIdx fs f τ) (x : fs.den N) (y : τ.den N),
    Fields.conv N I fs (FIdx.setS N i x y) = i.set (Fields.conv N I fs x) (Ty.conv N I τ y)
  | .cons .., _, _, .here, (_, _), _ => rfl
  | .cons .., _, _, .there i, (a, xs), y => by
    show (_, _) = (_, _)
    rw [FIdx.conv_setS i xs y]

theorem Sel.conv_pickS {src : Fields} : ∀ {fs : Fields} (sel : Sel src fs) (xs : src.den N),
    Fields.conv N I fs (Sel.pickS N sel xs) = sel.pick (Fields.conv N I src xs)
  | _, .nil, _ => rfl
  | _, .cons i rest, xs => by
    show (_, _) = (_, _)
    rw [FIdx.conv_getS, Sel.conv_pickS rest xs]
  | _, .absent _ rest, xs => by
    show (_, _) = (_, _)
    rw [Sel.conv_pickS rest xs]; rfl

theorem Upd.conv_applyS {src : Fields} : ∀ {fs : Fields} (u : Upd src fs) (xs : src.den N) (r : fs.den N),
    Fields.conv N I fs (Upd.applyS N u xs r) = u.apply (Fields.conv N I src xs) (Fields.conv N I fs r)
  | .nil, .nil, _, _ => rfl
  | .cons .., .set i rest, xs, (_, r) => by
    show (_, _) = (_, _)
    rw [FIdx.conv_getS, Upd.conv_applyS rest xs r]
  | .cons .., .keep _ rest, xs, (a, r) => by
    show (_, _) = (_, _)
    rw [Upd.conv_applyS rest xs r]

theorem recGet_conv {fs : Fields} {f : String} {τ : Ty} (i : FIdx fs f τ) (r : Ty.den N (.record fs)) :
    Ty.conv N I τ (recGet N I i r) = i.get (Ty.conv N I (.record fs) r) := FIdx.conv_getS I i _

theorem recSet_conv {fs : Fields} {f : String} {τ : Ty} (i : FIdx fs f τ) (r : Ty.den N (.record fs)) (y : τ.den N) :
    Ty.conv N I (.record fs) (recSet N I i r y) = i.set (Ty.conv N I (.record fs) r) (Ty.conv N I τ y) := by
  rw [recSet, Ty.conv_recMk, FIdx.conv_setS]; rfl

theorem recSel_conv {src fs : Fields} (sel : Sel src fs) (es : src.den N) :
    Ty.conv N I (.record fs) (recSel N I sel es) = sel.pick (Fields.conv N I src es) := by
  rw [recSel, Ty.conv_recMk, Sel.conv_pickS]

theorem recUpd_conv {src fs : Fields} (u : Upd src fs) (es : src.den N) (r : Ty.den N (.record fs)) :
    Ty.conv N I (.record fs) (recUpd N I u es r) = u.apply (Fields.conv N I src es) (Ty.conv N I (.record fs) r) := by
  rw [recUpd, Ty.conv_recMk, Upd.conv_applyS]; rfl

theorem Narrowing.conv_embedS : ∀ {σ τ : Ty} (M : Narrowing σ τ) (z : σ.den N),
    Ty.conv N I τ (Narrowing.embedS N I M z) = M.embed (Ty.conv N I σ z)
  | _, _, .some _ _, _ => rfl
  | _, _, .variant i, z => by
    simp only [Narrowing.embedS]
    rw [Ty.conv_unionMk, Variants.conv_injS]
    show _ = Narrowing.embed (.variant i) (Fields.conv N I _ (recView N I _ z))
    rw [Fields.conv_cons]
    rfl

theorem Ty.beqS_eq : ∀ (τ : Ty) (a b : τ.den N), Ty.beqS N τ a b = Ty.beq τ (Ty.conv N I τ a) (Ty.conv N I τ b)
  | .bool, _, _ | .int, _, _ | .number, _, _ | .string, _, _ | .tag _, _, _ | .lits _ _, _, _
  | .option _ _, _, _ | .record _, _, _ | .union _ _, _, _ | .array _, _, _ | .map _, _, _ => rfl

theorem Op.conv_applyS : ∀ {σ τ : Ty} (op : Op σ τ) (a b : σ.den N),
    Ty.conv N I τ (Op.applyS N op a b) = op.apply (Ty.conv N I σ a) (Ty.conv N I σ b)
  | _, _, .eq _, a, b => by simp only [Op.applyS, Op.apply, Ty.beqS_eq I]; rfl
  | _, _, .ne _, a, b => by simp only [Op.applyS, Op.apply, Ty.beqS_eq I]; rfl
  | _, _, .add, _, _ | _, _, .sub, _, _ | _, _, .mul, _, _ | _, _, .concat, _, _ | _, _, .lt, _, _
  | _, _, .le, _, _ | _, _, .gt, _, _ | _, _, .ge, _, _ | _, _, .slt, _, _ | _, _, .sle, _, _ | _, _, .sgt, _, _
  | _, _, .sge, _, _ | _, _, .nadd, _, _ | _, _, .nsub, _, _ | _, _, .nmul, _, _ | _, _, .nlt, _, _ | _, _, .nle, _, _
  | _, _, .ngt, _, _ | _, _, .nge, _, _ | _, _, .idiv, _, _ | _, _, .imod, _, _ | _, _, .ndiv, _, _
  | _, _, .nmod, _, _ => rfl

theorem Op.guardS_eq : ∀ {σ τ : Ty} (op : Op σ τ) (s : Bool) (a b : σ.den N),
    Op.guardS N op s a b = op.guard s (Ty.conv N I σ a) (Ty.conv N I σ b)
  | _, _, .eq _, _, _, _ | _, _, .ne _, _, _, _
  | _, _, .add, _, _, _ | _, _, .sub, _, _, _ | _, _, .mul, _, _, _ | _, _, .concat, _, _, _ | _, _, .lt, _, _, _
  | _, _, .le, _, _, _ | _, _, .gt, _, _, _ | _, _, .ge, _, _, _ | _, _, .slt, _, _, _ | _, _, .sle, _, _, _
  | _, _, .sgt, _, _, _ | _, _, .sge, _, _, _ | _, _, .nadd, _, _, _ | _, _, .nsub, _, _, _ | _, _, .nmul, _, _, _
  | _, _, .nlt, _, _, _ | _, _, .nle, _, _, _ | _, _, .ngt, _, _, _ | _, _, .nge, _, _, _ | _, _, .idiv, _, _, _
  | _, _, .imod, _, _, _ | _, _, .ndiv, _, _, _ | _, _, .nmod, _, _, _ => rfl

theorem SMethod.conv_applyS : ∀ {τ : Ty} (m : SMethod τ) (s t : JSString),
    Ty.conv N I τ (SMethod.applyS N m s t) = m.apply s t
  | _, .startsWith, _, _ | _, .endsWith, _, _ | _, .includes, _, _ | _, .indexOf, _, _ => rfl

mutual
  theorem Ty.conv_defaultS : ∀ (τ : Ty), Ty.conv N I τ (Ty.defaultS N I τ) = τ.default
    | .bool | .int | .number | .string | .tag _ | .lits _ _ | .option _ _ | .array _ | .map _ => rfl
    | .record fs => by
      show Ty.conv N I (.record fs) (recMk N I fs (Fields.defaultS N I fs)) = fs.default
      rw [Ty.conv_recMk, Fields.conv_defaultS]
    | .union _ vs => by
      show Ty.conv N I (.union _ vs) (unionMk N I vs (Variants.defaultS N I vs)) = vs.default
      rw [Ty.conv_unionMk, Variants.conv_defaultS]

  theorem Fields.conv_defaultS : ∀ (fs : Fields), Fields.conv N I fs (Fields.defaultS N I fs) = fs.default
    | .nil => rfl
    | .cons _ τ rest => by
      show (_, _) = (_, _)
      rw [Ty.conv_defaultS τ, Fields.conv_defaultS rest]

  theorem Variants.conv_defaultS : ∀ (vs : Variants), Variants.conv N I vs (Variants.defaultS N I vs) = vs.default
    | .one _ fs => Fields.conv_defaultS fs
    | .cons _ fs _ => by
      show Sum.inl _ = Sum.inl _
      rw [Fields.conv_defaultS fs]
end

mutual
  theorem Ty.conv_convInv : ∀ (τ : Ty) (x : τ.denote), Ty.conv N I τ (Ty.convInv N I τ x) = x
    | .bool, _ | .int, _ | .number, _ | .string, _ | .tag _, _ | .lits _ _, _ => rfl
    | .option _ τ, x => by
      cases x with
      | none => rfl
      | some y =>
        show some (Ty.conv N I τ (Ty.convInv N I τ y)) = some y
        rw [Ty.conv_convInv τ y]
    | .record fs, x => by
      show Ty.conv N I (.record fs) (recMk N I fs (Fields.convInv N I fs x)) = x
      rw [Ty.conv_recMk, Fields.conv_convInv]
    | .union _ vs, x => by
      show Ty.conv N I (.union _ vs) (unionMk N I vs (Variants.convInv N I vs x)) = x
      rw [Ty.conv_unionMk, Variants.conv_convInv]
    | .array τ, xs => by
      show List.map _ (List.map _ xs) = xs
      rw [List.map_map]
      conv => rhs; rw [← List.map_id xs]
      congr 1; funext y; exact Ty.conv_convInv τ y
    | .map τ, m => by
      show List.map _ (List.map _ m) = m
      rw [List.map_map]
      conv => rhs; rw [← List.map_id m]
      congr 1; funext p; obtain ⟨k, v⟩ := p
      show (k, Ty.conv N I τ (Ty.convInv N I τ v)) = (k, v)
      rw [Ty.conv_convInv τ v]

  theorem Fields.conv_convInv : ∀ (fs : Fields) (x : fs.denote), Fields.conv N I fs (Fields.convInv N I fs x) = x
    | .nil, () => rfl
    | .cons _ τ rest, (a, xs) => by
      show (_, _) = (_, _)
      rw [Ty.conv_convInv τ a, Fields.conv_convInv rest xs]

  theorem Variants.conv_convInv : ∀ (vs : Variants) (x : vs.denote), Variants.conv N I vs (Variants.convInv N I vs x) = x
    | .one _ fs, x => Fields.conv_convInv fs x
    | .cons _ fs _, .inl x => by
      show Sum.inl _ = _
      rw [Fields.conv_convInv fs x]
    | .cons _ _ rest, .inr y => by
      show Sum.inr _ = _
      rw [Variants.conv_convInv rest y]
end

mutual
  theorem Ty.convInv_conv : ∀ (τ : Ty) (x : τ.den N), Ty.convInv N I τ (Ty.conv N I τ x) = x
    | .bool, _ | .int, _ | .number, _ | .string, _ | .tag _, _ | .lits _ _, _ => rfl
    | .option _ τ, x => by
      cases x with
      | none => rfl
      | some y =>
        show some (Ty.convInv N I τ (Ty.conv N I τ y)) = some y
        rw [Ty.convInv_conv τ y]
    | .record fs, r => by
      show recMk N I fs (Fields.convInv N I fs (Fields.conv N I fs (recView N I fs r))) = r
      rw [Fields.convInv_conv, recMk_recView]
    | .union _ vs, u => by
      show unionMk N I vs (Variants.convInv N I vs (Variants.conv N I vs (unionView N I vs u))) = u
      rw [Variants.convInv_conv, unionMk_unionView]
    | .array τ, xs => by
      show List.map _ (List.map _ xs) = xs
      rw [List.map_map]
      conv => rhs; rw [← List.map_id xs]
      congr 1; funext y; exact Ty.convInv_conv τ y
    | .map τ, m => by
      show List.map _ (List.map _ m) = m
      rw [List.map_map]
      conv => rhs; rw [← List.map_id m]
      congr 1; funext p; obtain ⟨k, v⟩ := p
      show (k, Ty.convInv N I τ (Ty.conv N I τ v)) = (k, v)
      rw [Ty.convInv_conv τ v]

  theorem Fields.convInv_conv : ∀ (fs : Fields) (x : fs.den N), Fields.convInv N I fs (Fields.conv N I fs x) = x
    | .nil, () => rfl
    | .cons _ τ rest, (a, xs) => by
      show (_, _) = (_, _)
      rw [Ty.convInv_conv τ a, Fields.convInv_conv rest xs]

  theorem Variants.convInv_conv : ∀ (vs : Variants) (x : vs.den N), Variants.convInv N I vs (Variants.conv N I vs x) = x
    | .one _ fs, x => Fields.convInv_conv fs x
    | .cons _ fs _, .inl x => by
      show Sum.inl _ = _
      rw [Fields.convInv_conv fs x]
    | .cons _ _ rest, .inr y => by
      show Sum.inr _ = _
      rw [Variants.convInv_conv rest y]
end

theorem Ty.conv_injective (τ : Ty) {a b : τ.den N} (h : Ty.conv N I τ a = Ty.conv N I τ b) : a = b := by
  rw [← Ty.convInv_conv I τ a, h, Ty.convInv_conv]

end

/-! ## Environments, states, maps, lists and functions -/

section
variable {N : Names} (I : Isos N)

theorem Var.conv_getS : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) (ρ : Γ.denS N),
    Ty.conv N I τ (Var.getS N v ρ) = v.get (Ctx.conv N I Γ ρ)
  | (_, _) :: _, _, _, .here, (_, _) => rfl
  | (_, _) :: _, _, _, .there _ v, (_, ρ) => Var.conv_getS v ρ

theorem Var.conv_setS : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) (ρ : Γ.denS N) (y : τ.den N),
    Ctx.conv N I Γ (Var.setS N v ρ y) = v.set (Ctx.conv N I Γ ρ) (Ty.conv N I τ y)
  | (_, _) :: _, _, _, .here, (_, _), _ => rfl
  | (_, _) :: _, _, _, .there _ v, (_, ρ), y => by
    show (_, _) = (_, _)
    rw [Var.conv_setS v ρ y]

theorem Var.conv_narrowValS : ∀ {Γ : Ctx} {x : String} {τ σ : Ty} (v : Var Γ x τ) (ρ : Γ.denS N) (y : σ.den N),
    Ctx.conv N I (v.narrow σ) (Var.narrowValS N v ρ y) = v.narrowVal (Ctx.conv N I Γ ρ) (Ty.conv N I σ y)
  | (_, _) :: _, _, _, _, .here, (_, _), _ => rfl
  | (_, _) :: _, _, _, _, .there _ v, (_, ρ), y => by
    show (_, _) = (_, _)
    rw [Var.conv_narrowValS v ρ y]

theorem Var.conv_widenS : ∀ {Γ : Ctx} {x : String} {τ σ : Ty} (v : Var Γ x τ) (eS : σ.den N → τ.den N)
    (eC : σ.denote → τ.denote), (∀ z, Ty.conv N I τ (eS z) = eC (Ty.conv N I σ z)) → ∀ (ρ : (v.narrow σ).denS N),
    Ctx.conv N I Γ (Var.widenS N v eS ρ) = v.widen eC (Ctx.conv N I (v.narrow σ) ρ)
  | (_, _) :: _, _, _, _, .here, eS, eC, he, ρ => by
    obtain ⟨a, ρ⟩ := ρ
    show (_, _) = (_, _)
    rw [he a]; rfl
  | (_, _) :: _, _, _, _, .there _ v, eS, eC, he, ρ => by
    obtain ⟨a, ρ⟩ := ρ
    show (_, _) = (_, _)
    rw [Var.conv_widenS v eS eC he ρ]; rfl

theorem Ctx.conv_noneS : ∀ (ps : Ctx), Ctx.conv N I ps (Ctx.noneS N I ps) = Ctx.none ps
  | [] => rfl
  | (_, τ) :: ps => by
    cases τ <;> simp only [Ctx.noneS, Ctx.none, Ctx.conv, Ctx.conv_noneS ps, Ty.conv_defaultS] <;> rfl

theorem Ctx.convInv_conv : ∀ (Γ : Ctx) (ρ : Γ.denS N), Ctx.convInv N I Γ (Ctx.conv N I Γ ρ) = ρ
  | [], () => rfl
  | (_, τ) :: Γ, (a, ρ) => by
    show (_, _) = (_, _)
    rw [Ty.convInv_conv, Ctx.convInv_conv Γ ρ]

theorem Ctx.conv_convInv : ∀ (Γ : Ctx) (ρ : Γ.denote), Ctx.conv N I Γ (Ctx.convInv N I Γ ρ) = ρ
  | [], () => rfl
  | (_, τ) :: Γ, (a, ρ) => by
    show (_, _) = (_, _)
    rw [Ty.conv_convInv, Ctx.conv_convInv Γ ρ]

/-! ### States -/

theorem Ctx.tupConv_tconsS : ∀ {x : String} {τ : Ty} {Δ : Ctx} (a : τ.den N) (t : Δ.tupS N),
    Ctx.tupConv N I ((x, τ) :: Δ) (Ctx.tconsS N a t) = Ctx.tcons (Ty.conv N I τ a) (Ctx.tupConv N I Δ t)
  | _, _, [], _, _ => rfl
  | _, _, _ :: _, _, _ => rfl

theorem Ctx.conv_theadS : ∀ {x : String} {τ : Ty} {Δ : Ctx} (t : Ctx.tupS N ((x, τ) :: Δ)),
    Ty.conv N I τ (Ctx.theadS N t) = Ctx.thead (Ctx.tupConv N I ((x, τ) :: Δ) t)
  | _, _, [], _ => rfl
  | _, _, _ :: _, (_, _) => rfl

theorem Ctx.tupConv_ttailS : ∀ {x : String} {τ : Ty} {Δ : Ctx} (t : Ctx.tupS N ((x, τ) :: Δ)),
    Ctx.tupConv N I Δ (Ctx.ttailS N t) = Ctx.ttail (Ctx.tupConv N I ((x, τ) :: Δ) t)
  | _, _, [], _ => rfl
  | _, _, _ :: _, (_, _) => rfl

theorem Ctx.tupConv_projS : ∀ (Γ : Ctx) (m : Mask) (ρ : Γ.denS N),
    Ctx.tupConv N I (Γ.sub m) (Ctx.projS N Γ m ρ) = Ctx.proj Γ m (Ctx.conv N I Γ ρ)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | (_, _) :: Γ, true :: m, (a, ρ) => by
    simp only [Ctx.projS, Ctx.proj, Ctx.conv]
    rw [Ctx.tupConv_tconsS, Ctx.tupConv_projS Γ m ρ]
  | (_, _) :: Γ, false :: m, (a, ρ) => by
    simp only [Ctx.projS, Ctx.proj, Ctx.conv]
    exact Ctx.tupConv_projS Γ m ρ

theorem Ctx.conv_mergeS : ∀ (Γ : Ctx) (m : Mask) (ρ : Γ.denS N) (s : (Γ.sub m).tupS N),
    Ctx.conv N I Γ (Ctx.mergeS N Γ m ρ s) = Ctx.merge Γ m (Ctx.conv N I Γ ρ) (Ctx.tupConv N I (Γ.sub m) s)
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | (_, _) :: Γ, true :: m, (a, ρ), s => by
    simp only [Ctx.mergeS, Ctx.merge, Ctx.conv]
    rw [Ctx.conv_theadS, Ctx.conv_mergeS Γ m ρ, Ctx.tupConv_ttailS]
  | (_, _) :: Γ, false :: m, (a, ρ), s => by
    simp only [Ctx.mergeS, Ctx.merge, Ctx.conv]
    rw [Ctx.conv_mergeS Γ m ρ s]

/-! ### Maps and lists -/

/-- A map's values converted. -/
abbrev mapConv {α β : Type} (f : α → β) (m : List (JSString × α)) : List (JSString × β) := m.map fun p => (p.1, f p.2)

theorem mapGet_conv {α β : Type} (f : α → β) : ∀ (m : List (JSString × α)) (k : JSString),
    mapGet (mapConv f m) k = (mapGet m k).map f
  | [], _ => rfl
  | (k', v) :: m, k => by
    have ih := mapGet_conv f m k
    simp only [mapGet, List.map_cons, List.lookup_cons] at ih ⊢
    split <;> simp_all

theorem mapPut_conv {α β : Type} (f : α → β) : ∀ (m : List (JSString × α)) (k : JSString) (v : α),
    mapConv f (mapPut m k v) = mapPut (mapConv f m) k (f v)
  | [], _, _ => rfl
  | (k', w) :: m, k, v => by
    simp only [mapPut, List.map_cons]
    split <;> simp [mapPut_conv f m k v]

theorem mapDel_conv {α β : Type} (f : α → β) (m : List (JSString × α)) (k : JSString) :
    mapConv f (mapDel m k) = mapDel (mapConv f m) k := by
  simp only [mapDel, mapConv, List.filter_map]; rfl

theorem listIndex_map {α β : Type} (f : α → β) (xs : List α) (i : Int) :
    listIndex (xs.map f) i = (listIndex xs i).map f := by
  simp only [listIndex]; split <;> simp

theorem signs_map {α β : Type} (f : α → β) (cS : α → α → Int) (cC : β → β → Int) (hc : ∀ a b, cC (f a) (f b) = cS a b)
    (xs : List α) : signs cC (xs.map f) = signs cS xs := by
  simp only [signs, List.map_map, Function.comp_def, hc]

theorem sortedBy_map {α β : Type} (f : α → β) (cS : α → α → Int) (cC : β → β → Int)
    (hc : ∀ a b, cC (f a) (f b) = cS a b) (xs : List α) : sortedBy cC (xs.map f) = (sortedBy cS xs).map f := by
  simp only [sortedBy, signs_map f cS cC hc, List.length_map, List.map_filterMap, List.getElem?_map]

theorem anySafe_map {α β : Type} (f : α → β) (pS sS : α → Bool) (pC sC : β → Bool) (hp : ∀ a, pC (f a) = pS a)
    (hs : ∀ a, sC (f a) = sS a) : ∀ (xs : List α), anySafe pC sC (xs.map f) = anySafe pS sS xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, anySafe, hp, hs, anySafe_map f pS sS pC sC hp hs xs]

theorem allSafe_map {α β : Type} (f : α → β) (pS sS : α → Bool) (pC sC : β → Bool) (hp : ∀ a, pC (f a) = pS a)
    (hs : ∀ a, sC (f a) = sS a) : ∀ (xs : List α), allSafe pC sC (xs.map f) = allSafe pS sS xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, allSafe, hp, hs, allSafe_map f pS sS pC sC hp hs xs]

theorem sortSafe_map {α β : Type} (f : α → β) (cS : α → α → Int) (cC : β → β → Int) (t : Bool)
    (sS : α → α → Bool) (sC : β → β → Bool) (hc : ∀ a b, cC (f a) (f b) = cS a b) (hs : ∀ a b, sC (f a) (f b) = sS a b)
    (xs : List α) : sortSafe cC t sC (xs.map f) = sortSafe cS t sS xs := by
  simp only [sortSafe, signs_map f cS cC hc, List.all_map, Function.comp_def, hs]

/-! ### Functions -/

theorem FVar.conv_getS : ∀ {Φ : Sigs} {g : String} {s : Sig} (fn : FVar Φ g s) (fs : Φ.denS N) (args : s.params.denS N),
    Ty.conv N I s.result (FVar.getS N fn fs args) = fn.get (Sigs.canon N I Φ fs) (Ctx.conv N I s.params args)
  | _ :: _, _, _, .here, (_, _), args => by
    simp only [FVar.getS, FVar.get, Sigs.canon, Ctx.convInv_conv]
  | _ :: _, _, _, .there fn, (_, fs), args => FVar.conv_getS fn fs args

theorem FVar.safeS_eq : ∀ {Φ : Sigs} {g : String} {s : Sig} (fn : FVar Φ g s) (ss : Φ.safetyS N) (args : s.params.denS N),
    FVar.safeS N fn ss args = fn.safe (Sigs.canonSafety N I Φ ss) (Ctx.conv N I s.params args)
  | _ :: _, _, _, .here, (_, _), args => by
    simp only [FVar.safeS, FVar.safe, Sigs.canonSafety, Ctx.convInv_conv]
  | _ :: _, _, _, .there fn, (_, ss), args => FVar.safeS_eq fn ss args

end

/-! ## Expressions -/

section
variable {N : Names} (I : Isos N) {Φ : Sigs} (fs : Φ.denS N)

mutual
  theorem TExpr.conv_denS : ∀ {Γ : Ctx} {τ : Ty} (e : TExpr Φ Γ τ) (ρ : Γ.denS N),
      Ty.conv N I τ (TExpr.denS N I fs e ρ) = e.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ)
    | _, _, .bool _, _ | _, _, .int _, _ | _, _, .str _, _ | _, _, .tagLit _, _ | _, _, .litIn .., _
    | _, _, .undef .., _ | _, _, .null .., _ | _, _, .num _, _ | _, _, .negNum .., _ | _, _, .newMap _, _ => rfl
    | _, _, .var v, ρ => Var.conv_getS I v ρ
    | _, _, .widen M e, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [Narrowing.conv_embedS, TExpr.conv_denS e ρ]
    | _, _, .not e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .neg e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .nneg e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .iinc _ e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .ninc _ e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .slength e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, h]; rfl
    | _, _, .bin op a b, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [Op.conv_applyS, TExpr.conv_denS a ρ, TExpr.conv_denS b ρ]
    | _, _, .and a b, ρ => by
      have ha : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS a ρ
      have hb : TExpr.denS N I fs b ρ = _ := TExpr.conv_denS b ρ
      simp only [TExpr.denS, TExpr.denote, ha, hb]; rfl
    | _, _, .or a b, ρ => by
      have ha : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS a ρ
      have hb : TExpr.denS N I fs b ρ = _ := TExpr.conv_denS b ρ
      simp only [TExpr.denS, TExpr.denote, ha, hb]; rfl
    | _, _, .cond c a b, ρ => by
      have hc : TExpr.denS N I fs c ρ = _ := TExpr.conv_denS c ρ
      simp only [TExpr.denS, TExpr.denote, hc]
      split
      · exact TExpr.conv_denS a ρ
      · exact TExpr.conv_denS b ρ
    | _, _, .isNull _ e, ρ => by
      have h := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, ← h]
      cases TExpr.denS N I fs e ρ <;> rfl
    | _, _, .notNull _ e, ρ => by
      have h := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, ← h]
      cases TExpr.denS N I fs e ρ <;> rfl
    | _, _, .condNull v _ a b, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TExpr.denS, TExpr.denote, ← hv]
      rcases Var.getS N v ρ with _ | y
      · exact TExpr.conv_denS a ρ
      · show _ = b.denote _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS, TExpr.conv_denS b]
    | _, _, .condNotNull v _ a b, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TExpr.denS, TExpr.denote, ← hv]
      rcases Var.getS N v ρ with _ | y
      · exact TExpr.conv_denS b ρ
      · show _ = a.denote _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS, TExpr.conv_denS a]
    | _, _, .coalesce _ a b, ρ => by
      have h := TExpr.conv_denS a ρ
      simp only [TExpr.denS, TExpr.denote, ← h]
      rcases TExpr.denS N I fs a ρ with _ | x
      · exact TExpr.conv_denS b ρ
      · rfl
    | _, _, .call fn _ args, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [FVar.conv_getS, TArgs.conv_denS args ρ]
    | _, _, .record es sel _, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [recSel_conv, TEntries.conv_denS es ρ]
    | _, _, .update r es u _, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [recUpd_conv, TEntries.conv_denS es ρ, TExpr.conv_denS r ρ]
    | _, _, .field e i _, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      rw [recGet_conv, TExpr.conv_denS e ρ]
    | _, _, .array es, ρ => TElems.conv_denS es ρ
    | _, _, .length a, ρ => by
      have h := TExpr.conv_denS a ρ
      simp only [TExpr.denS, TExpr.denote, ← h]
      show ((TExpr.denS N I fs a ρ).length : Int) = ((List.map _ _).length : Int)
      rw [List.length_map]
    | _, _, .smethod m a b, ρ => by
      have ha : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS a ρ
      have hb : TExpr.denS N I fs b ρ = _ := TExpr.conv_denS b ρ
      simp only [TExpr.denS, TExpr.denote, ha, hb]
      exact SMethod.conv_applyS I m _ _
    | _, _, .slice1 a b, ρ => by
      have ha : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS a ρ
      have hb : TExpr.denS N I fs b ρ = _ := TExpr.conv_denS b ρ
      simp only [TExpr.denS, TExpr.denote, ha, hb]; rfl
    | _, _, .slice2 a b c, ρ => by
      have ha : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS a ρ
      have hb : TExpr.denS N I fs b ρ = _ := TExpr.conv_denS b ρ
      have hc : TExpr.denS N I fs c ρ = _ := TExpr.conv_denS c ρ
      simp only [TExpr.denS, TExpr.denote, ha, hb, hc]; rfl
    | _, _, .index a i, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hi : TExpr.denS N I fs i ρ = _ := TExpr.conv_denS i ρ
      simp only [TExpr.denS, TExpr.denote, ← ha, hi]
      exact (listIndex_map _ _ _).symm
    | _, _, .includes _ a e, ρ => by
      have ha := TExpr.conv_denS a ρ
      have he := TExpr.conv_denS e ρ
      simp only [TExpr.denS, TExpr.denote, ← ha, ← he]
      show List.any _ _ = List.any (List.map _ _) _
      rw [List.any_map]
      simp only [Function.comp_def, Ty.beqS_eq I]
    | _, _, .any a p, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hp : ∀ y, TFn.denS N I fs p ρ y = _ := TFn.conv_denS p ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      show List.any _ _ = List.any (List.map _ _) _
      rw [List.any_map]
      simp only [Function.comp_def, ← hp]
    | _, _, .all a p, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hp : ∀ y, TFn.denS N I fs p ρ y = _ := TFn.conv_denS p ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      show List.all _ _ = List.all (List.map _ _) _
      rw [List.all_map]
      simp only [Function.comp_def, ← hp]
    | _, _, .find a p, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hp : ∀ y, TFn.denS N I fs p ρ y = _ := TFn.conv_denS p ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      show Option.map _ _ = List.find? _ (List.map _ _)
      rw [List.find?_map]
      simp only [Function.comp_def, ← hp]
    | _, _, .filter a p, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hp : ∀ y, TFn.denS N I fs p ρ y = _ := TFn.conv_denS p ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      show List.map _ _ = List.filter _ (List.map _ _)
      rw [List.filter_map]
      simp only [Function.comp_def, ← hp]
    | _, _, .map a f, ρ => by
      have ha := TExpr.conv_denS a ρ
      have hf := TFn.conv_denS f ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      show List.map _ (List.map _ _) = List.map _ (List.map _ _)
      simp only [List.map_map, Function.comp_def, hf]
    | _, _, .sorted a c, ρ => by
      have ha := TExpr.conv_denS a ρ
      simp only [TExpr.denS, TExpr.denote, ← ha]
      exact (sortedBy_map _ _ _ (fun y z => (TCmp.conv_denS c ρ y z).symm) _).symm
    | _, _, .stateGet v i _ k, ρ => by
      have hv := Var.conv_getS I v ρ
      have hk : TExpr.denS N I fs k ρ = _ := TExpr.conv_denS k ρ
      simp only [TExpr.denS, TExpr.denote, ← hv, hk]
      rw [← recGet_conv I i]
      exact (mapGet_conv _ _ _).symm
    | _, _, .stateHas v i k, ρ => by
      have hv := Var.conv_getS I v ρ
      have hk : TExpr.denS N I fs k ρ = _ := TExpr.conv_denS k ρ
      simp only [TExpr.denS, TExpr.denote, ← hv, hk]
      rw [← recGet_conv I i]
      show _ = Option.isSome (mapGet (mapConv _ _) _)
      rw [mapGet_conv]
      cases mapGet _ _ <;> rfl
    | _, _, .stateSize v i, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TExpr.denS, TExpr.denote, ← hv]
      rw [← recGet_conv I i]
      show _ = ((List.map _ _).length : Int)
      rw [List.length_map]; rfl
    | _, _, .callThis fn v args, ρ => by
      simp only [TExpr.denS, TExpr.denote]
      refine (FVar.conv_getS I fn fs _).trans ?_
      show fn.get _ (Ty.conv N I _ (Var.getS N v ρ), Ctx.conv N I _ (TArgs.denS N I fs args ρ)) = _
      rw [Var.conv_getS, TArgs.conv_denS args ρ]

  theorem TArgs.conv_denS : ∀ {Γ : Ctx} {ps : Ctx} (args : TArgs Φ Γ ps) (ρ : Γ.denS N),
      Ctx.conv N I ps (TArgs.denS N I fs args ρ) = args.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ => rfl
    | _, _, .cons e rest, ρ => by
      show (_, _) = (_, _)
      rw [TExpr.conv_denS e ρ, TArgs.conv_denS rest ρ]
    | _, _, .omitted _, _ => Ctx.conv_noneS I _

  theorem TEntries.conv_denS : ∀ {Γ : Ctx} {src : Fields} (es : TEntries Φ Γ src) (ρ : Γ.denS N),
      Fields.conv N I src (TEntries.denS N I fs es ρ) = es.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ => rfl
    | _, _, .cons _ e rest, ρ => by
      show (_, _) = (_, _)
      rw [TExpr.conv_denS e ρ, TEntries.conv_denS rest ρ]

  theorem TFn.conv_denS : ∀ {Γ : Ctx} {τ σ : Ty} (p : TFn Φ Γ τ σ) (ρ : Γ.denS N) (y : τ.den N),
      Ty.conv N I σ (TFn.denS N I fs p ρ y) = p.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ) (Ty.conv N I τ y)
    | _, _, _, .arrow _ body, ρ, y => TExpr.conv_denS body (y, ρ)
    | _, _, _, .const body, ρ, _ => TExpr.conv_denS body ρ
    | _, _, _, .ref fn _, _, y => FVar.conv_getS I fn fs (y, ())

  theorem TCmp.conv_denS : ∀ {Γ : Ctx} {τ : Ty} (c : TCmp Φ Γ τ) (ρ : Γ.denS N) (y z : τ.den N),
      TCmp.denS N I fs c ρ y z = c.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ) (Ty.conv N I τ y) (Ty.conv N I τ z)
    | _, _, .arrow _ _ body, ρ, y, z => TExpr.conv_denS body (y, z, ρ)
    | _, _, .ref fn _, _, y, z => FVar.conv_getS I fn fs (y, z, ())

  theorem TElems.conv_denS : ∀ {Γ : Ctx} {τ : Ty} (es : TElems Φ Γ τ) (ρ : Γ.denS N),
      (TElems.denS N I fs es ρ).map (Ty.conv N I τ) = es.denote (Sigs.canon N I Φ fs) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ => rfl
    | _, _, .cons e rest, ρ => by
      simp only [TElems.denS, TElems.denote, List.map_cons, TExpr.conv_denS e ρ, TElems.conv_denS rest ρ]
    | _, _, .spread a rest, ρ => by
      simp only [TElems.denS, TElems.denote, List.map_append, TElems.conv_denS rest ρ]
      rw [← TExpr.conv_denS a ρ]; rfl
    | _, _, .spreadKeys v i rest, ρ => by
      simp only [TElems.denS, TElems.denote, List.map_append, TElems.conv_denS rest ρ]
      rw [← Var.conv_getS I v ρ, ← recGet_conv I i]
      congr 1
      show _ = List.map Prod.fst (List.map _ _)
      simp only [List.map_map]; rfl
    | _, _, .spreadValues v i rest, ρ => by
      simp only [TElems.denS, TElems.denote, List.map_append, TElems.conv_denS rest ρ]
      rw [← Var.conv_getS I v ρ, ← recGet_conv I i]
      congr 1
      show _ = List.map Prod.snd (List.map _ _)
      simp only [List.map_map]; rfl
end

end

/-! ## Safety of expressions -/

section
variable {N : Names} (I : Isos N) {Φ : Sigs} (fs : Φ.denS N) (ss : Φ.safetyS N)

mutual
  theorem TExpr.safeS_eq : ∀ {Γ : Ctx} {τ : Ty} (e : TExpr Φ Γ τ) (ρ : Γ.denS N),
      TExpr.safeS N I fs ss e ρ = e.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ)
    | _, _, .bool _, _ | _, _, .int _, _ | _, _, .str _, _ | _, _, .tagLit _, _ | _, _, .litIn .., _
    | _, _, .undef .., _ | _, _, .null .., _ | _, _, .num _, _ | _, _, .negNum .., _ | _, _, .newMap _, _
    | _, _, .var _, _ | _, _, .stateSize _ _, _ => rfl
    | _, _, .widen _ e, ρ | _, _, .not e, ρ | _, _, .neg e, ρ | _, _, .isNull _ e, ρ | _, _, .notNull _ e, ρ
    | _, _, .field e _ _, ρ | _, _, .iinc _ e, ρ | _, _, .length e, ρ | _, _, .slength e, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; exact TExpr.safeS_eq e ρ
    | _, _, .index a b, ρ | _, _, .includes _ a b, ρ | _, _, .smethod _ a b, ρ | _, _, .slice1 a b, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; rw [TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ]
    | _, _, .slice2 a b c, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; rw [TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ, TExpr.safeS_eq c ρ]
    | _, _, .bin op a b, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [Op.guardS_eq I, TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ, TExpr.conv_denS I fs a ρ, TExpr.conv_denS I fs b ρ]
    | _, _, .nneg e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS I fs e ρ
      simp only [TExpr.safeS, TExpr.safe, h, TExpr.safeS_eq e ρ]
    | _, _, .ninc _ e, ρ => by
      have h : TExpr.denS N I fs e ρ = _ := TExpr.conv_denS I fs e ρ
      simp only [TExpr.safeS, TExpr.safe, h, TExpr.safeS_eq e ρ]
    | _, _, .and a b, ρ => by
      have h : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS I fs a ρ
      simp only [TExpr.safeS, TExpr.safe, h, TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ]
    | _, _, .or a b, ρ => by
      have h : TExpr.denS N I fs a ρ = _ := TExpr.conv_denS I fs a ρ
      simp only [TExpr.safeS, TExpr.safe, h, TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ]
    | _, _, .cond c a b, ρ => by
      have h : TExpr.denS N I fs c ρ = _ := TExpr.conv_denS I fs c ρ
      simp only [TExpr.safeS, TExpr.safe, h, TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ, TExpr.safeS_eq c ρ]
    | _, _, .condNull v _ a b, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TExpr.safeS, TExpr.safe, ← hv]
      rcases Var.getS N v ρ with _ | y
      · simp only [TExpr.safeS_eq a ρ]; rfl
      · show _ = (b.trivial || b.safe _ _ (v.narrowVal _ (Ty.conv N I _ y)))
        rw [← Var.conv_narrowValS, ← TExpr.safeS_eq b]
    | _, _, .condNotNull v _ a b, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TExpr.safeS, TExpr.safe, ← hv]
      rcases Var.getS N v ρ with _ | y
      · simp only [TExpr.safeS_eq b ρ]; rfl
      · show _ = (a.trivial || a.safe _ _ (v.narrowVal _ (Ty.conv N I _ y)))
        rw [← Var.conv_narrowValS, ← TExpr.safeS_eq a]
    | _, _, .coalesce _ a b, ρ => by
      have h := TExpr.conv_denS I fs a ρ
      simp only [TExpr.safeS, TExpr.safe, ← h, TExpr.safeS_eq a ρ, TExpr.safeS_eq b ρ]
      rcases TExpr.denS N I fs a ρ with _ | x <;> rfl
    | _, _, .call fn _ args, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [FVar.safeS_eq I, TArgs.conv_denS I fs args ρ, TArgs.safeS_eq args ρ]
    | _, _, .record es _ _, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; exact TEntries.safeS_eq es ρ
    | _, _, .array es, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; exact TElems.safeS_eq es ρ
    | _, _, .update r es _ _, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; rw [TExpr.safeS_eq r ρ, TEntries.safeS_eq es ρ]
    | _, _, .any a p, ρ | _, _, .find a p, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [TExpr.safeS_eq a ρ, ← TExpr.conv_denS I fs a ρ]
      congr 1
      exact (anySafe_map _ _ _ _ _ (fun y => (TFn.conv_denS I fs p ρ y).symm) (fun y => (TFn.safeS_eq p ρ y).symm) _).symm
    | _, _, .all a p, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [TExpr.safeS_eq a ρ, ← TExpr.conv_denS I fs a ρ]
      congr 1
      exact (allSafe_map _ _ _ _ _ (fun y => (TFn.conv_denS I fs p ρ y).symm) (fun y => (TFn.safeS_eq p ρ y).symm) _).symm
    | _, _, .filter a p, ρ | _, _, .map a p, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [TExpr.safeS_eq a ρ, ← TExpr.conv_denS I fs a ρ]
      congr 1
      show List.all _ _ = List.all (List.map _ _) _
      rw [List.all_map]
      congr 1; funext y; exact TFn.safeS_eq p ρ y
    | _, _, .sorted a c, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [TExpr.safeS_eq a ρ, ← TExpr.conv_denS I fs a ρ]
      congr 1
      exact (sortSafe_map _ _ _ _ _ _ (fun y z => (TCmp.conv_denS I fs c ρ y z).symm)
        (fun y z => (TCmp.safeS_eq c ρ y z).symm) _).symm
    | _, _, .stateGet _ _ _ k, ρ | _, _, .stateHas _ _ k, ρ => by
      simp only [TExpr.safeS, TExpr.safe]; exact TExpr.safeS_eq k ρ
    | _, _, .callThis fn v args, ρ => by
      simp only [TExpr.safeS, TExpr.safe]
      rw [TArgs.safeS_eq args ρ, FVar.safeS_eq I]
      congr 2
      show (Ty.conv N I _ (Var.getS N v ρ), Ctx.conv N I _ (TArgs.denS N I fs args ρ)) = _
      rw [Var.conv_getS, TArgs.conv_denS I fs args ρ]

  theorem TArgs.safeS_eq : ∀ {Γ : Ctx} {ps : Ctx} (args : TArgs Φ Γ ps) (ρ : Γ.denS N),
      TArgs.safeS N I fs ss args ρ = args.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ | _, _, .omitted _, _ => rfl
    | _, _, .cons e rest, ρ => by
      simp only [TArgs.safeS, TArgs.safe]; rw [TExpr.safeS_eq e ρ, TArgs.safeS_eq rest ρ]

  theorem TEntries.safeS_eq : ∀ {Γ : Ctx} {src : Fields} (es : TEntries Φ Γ src) (ρ : Γ.denS N),
      TEntries.safeS N I fs ss es ρ = es.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ => rfl
    | _, _, .cons _ e rest, ρ => by
      simp only [TEntries.safeS, TEntries.safe]; rw [TExpr.safeS_eq e ρ, TEntries.safeS_eq rest ρ]

  theorem TFn.safeS_eq : ∀ {Γ : Ctx} {τ σ : Ty} (p : TFn Φ Γ τ σ) (ρ : Γ.denS N) (y : τ.den N),
      TFn.safeS N I fs ss p ρ y = p.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ) (Ty.conv N I τ y)
    | _, _, _, .arrow _ body, ρ, y => TExpr.safeS_eq body (y, ρ)
    | _, _, _, .const body, ρ, _ => TExpr.safeS_eq body ρ
    | _, _, _, .ref fn _, _, y => FVar.safeS_eq I fn ss (y, ())

  theorem TCmp.safeS_eq : ∀ {Γ : Ctx} {τ : Ty} (c : TCmp Φ Γ τ) (ρ : Γ.denS N) (y z : τ.den N),
      TCmp.safeS N I fs ss c ρ y z =
        c.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ) (Ty.conv N I τ y) (Ty.conv N I τ z)
    | _, _, .arrow _ _ body, ρ, y, z => TExpr.safeS_eq body (y, z, ρ)
    | _, _, .ref fn _, _, y, z => FVar.safeS_eq I fn ss (y, z, ())

  theorem TElems.safeS_eq : ∀ {Γ : Ctx} {τ : Ty} (es : TElems Φ Γ τ) (ρ : Γ.denS N),
      TElems.safeS N I fs ss es ρ = es.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) (Ctx.conv N I Γ ρ)
    | _, _, .nil, _ => rfl
    | _, _, .cons e rest, ρ | _, _, .spread e rest, ρ => by
      simp only [TElems.safeS, TElems.safe]; rw [TExpr.safeS_eq e ρ, TElems.safeS_eq rest ρ]
    | _, _, .spreadKeys _ _ rest, ρ | _, _, .spreadValues _ _ rest, ρ => by
      simp only [TElems.safeS, TElems.safe]; exact TElems.safeS_eq rest ρ
end

end

end Ariadne

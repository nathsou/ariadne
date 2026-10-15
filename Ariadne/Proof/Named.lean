import Ariadne.Typed.Named
import Ariadne.Proof.Idiom
import Ariadne.Proof.Adequacy
import Ariadne.Proof.Frame

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

theorem Ty.conv_mapPut (σ : Ty) (m : Ty.den N (.map σ)) (k : JSString) (v : σ.den N) :
    Ty.conv N I (.map σ) (mapPut m k v) = mapPut (Ty.conv N I (.map σ) m) k (Ty.conv N I σ v) := mapPut_conv _ m k v

theorem Ty.conv_mapDel (σ : Ty) (m : Ty.den N (.map σ)) (k : JSString) :
    Ty.conv N I (.map σ) (mapDel m k) = mapDel (Ty.conv N I (.map σ) m) k := mapDel_conv _ m k

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

/-! ## Loops and cases through a conversion -/

theorem foldl_conv {α β σ σ' : Type} (g : α → β) (f : σ → σ') (stepS : σ → α → σ) (stepC : σ' → β → σ')
    (hs : ∀ s y, f (stepS s y) = stepC (f s) (g y)) : ∀ (xs : List α) (s : σ),
    f (xs.foldl stepS s) = (xs.map g).foldl stepC (f s)
  | [], _ => rfl
  | y :: ys, s => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_conv g f stepS stepC hs ys, hs]

theorem forIn_conv {α β σ σ' R R' : Type} (g : α → β) (fσ : σ → σ') (h : R → R')
    (stepS : α → (σ → R) → (σ → R) → σ → R) (stepC : β → (σ' → R') → (σ' → R') → σ' → R')
    (hs : ∀ y nS eS nC eC s, (∀ s', h (nS s') = nC (fσ s')) → (∀ s', h (eS s') = eC (fσ s')) →
      h (stepS y nS eS s) = stepC (g y) nC eC (fσ s))
    (exitS : σ → R) (exitC : σ' → R') (he : ∀ s, h (exitS s) = exitC (fσ s)) :
    ∀ (xs : List α) (s : σ), h (forIn xs stepS exitS s) = forIn (xs.map g) stepC exitC (fσ s)
  | [], s => he s
  | y :: ys, s => hs y _ _ _ _ s (fun s' => forIn_conv g fσ h stepS stepC hs exitS exitC he ys s') he

theorem whileIn_conv {σ σ' R R' : Type} (fσ : σ → σ') (h : R → R') (condS : σ → Bool) (condC : σ' → Bool)
    (hc : ∀ s, condS s = condC (fσ s)) (stepS : (σ → R) → (σ → R) → σ → R) (stepC : (σ' → R') → (σ' → R') → σ' → R')
    (hs : ∀ nS eS nC eC s, (∀ s', h (nS s') = nC (fσ s')) → (∀ s', h (eS s') = eC (fσ s')) →
      h (stepS nS eS s) = stepC nC eC (fσ s))
    (exitS stuckS : σ → R) (exitC stuckC : σ' → R') (he : ∀ s, h (exitS s) = exitC (fσ s))
    (hst : ∀ s, h (stuckS s) = stuckC (fσ s)) :
    ∀ (n : Nat) (s : σ), h (whileIn n condS stepS exitS stuckS s) = whileIn n condC stepC exitC stuckC (fσ s)
  | 0, s => hst s
  | n + 1, s => by
    rw [whileIn_succ, whileIn_succ, hc]
    split
    · exact hs _ _ _ _ s (fun s' => whileIn_conv fσ h condS condC hc stepS stepC hs exitS stuckS exitC stuckC he hst n s') he
    · exact he s

theorem Variants.elimS_congr {N : Names} {R : Type} : ∀ (vs : Variants) (x : vs.den N)
    (k k' : ∀ {t fs}, VIdx vs t fs → fs.den N → R), (∀ {t fs} (i : VIdx vs t fs) y, k i y = k' i y) →
    Variants.elimS N vs x k = Variants.elimS N vs x k'
  | .one _ _, _, _, _, h => h _ _
  | .cons _ _ _, .inl _, _, _, h => h _ _
  | .cons _ _ rest, .inr w, k, k', h => Variants.elimS_congr rest w _ _ fun i y => h (.there i) y

/-! ## Statements -/

section
variable {N : Names} (I : Isos N) {Φ : Sigs} (fs : Φ.denS N)

/-- Continuations that give, through `h`, what the denotation's do on the converted environments. -/
def KRel {Γ : Ctx} {RS RC : Type} (h : RS → RC) (kS : KS N Γ RS) (kC : K Γ RC) : Prop :=
  ∀ ρ, h (kS.normal ρ) = kC.normal (Ctx.conv N I Γ ρ) ∧ h (kS.brk ρ) = kC.brk (Ctx.conv N I Γ ρ) ∧
    h (kS.cont ρ) = kC.cont (Ctx.conv N I Γ ρ)

theorem KRel.map {Γ Γ' : Ctx} {RS RC : Type} {h : RS → RC} {kS : KS N Γ RS} {kC : K Γ RC}
    (fS : Γ'.denS N → Γ.denS N) (fC : Γ'.denote → Γ.denote) (hf : ∀ ρ, Ctx.conv N I Γ (fS ρ) = fC (Ctx.conv N I Γ' ρ))
    (hk : KRel I h kS kC) : KRel I h (kS.map fS) (kC.map fC) := fun ρ => by
  simp only [KS.map, K.map, Function.comp, ← hf]; exact hk (fS ρ)

theorem KRel.snd {x : String} {σ : Ty} {Γ : Ctx} {RS RC : Type} {h : RS → RC} {kS : KS N Γ RS} {kC : K Γ RC}
    (hk : KRel I h kS kC) : KRel I (Γ := (x, σ) :: Γ) h (kS.map Prod.snd) (kC.map Prod.snd) :=
  KRel.map (Γ' := (x, σ) :: Γ) I Prod.snd Prod.snd (fun ρ => by obtain ⟨a, ρ⟩ := ρ; rfl) hk

theorem KRel.normal {Γ : Ctx} {RS RC : Type} {h : RS → RC} {kS : KS N Γ RS} {kC : K Γ RC}
    {nS : Γ.denS N → RS} {nC : Γ.denote → RC} (hn : ∀ ρ, h (nS ρ) = nC (Ctx.conv N I Γ ρ)) (hk : KRel I h kS kC) :
    KRel I h { kS with normal := nS } { kC with normal := nC } := fun ρ => ⟨hn ρ, (hk ρ).2⟩

theorem KRel.all {Γ : Ctx} {RS RC : Type} {h : RS → RC} {nS : Γ.denS N → RS} {nC : Γ.denote → RC}
    (hn : ∀ ρ, h (nS ρ) = nC (Ctx.conv N I Γ ρ)) : KRel I h (KS.all nS) (K.all nC) := fun ρ => ⟨hn ρ, hn ρ, hn ρ⟩

theorem KRel.widen {Γ : Ctx} {x : String} {σ : Ty} {n : Nullish} {RS RC : Type} {h : RS → RC} {kS : KS N Γ RS}
    {kC : K Γ RC} (v : Var Γ x (.option n σ)) (hk : KRel I h kS kC) :
    KRel I h (kS.map (Var.widenS N v some)) (kC.map (v.widen some)) :=
  KRel.map I _ _ (Var.conv_widenS I v some some (fun _ => rfl)) hk

theorem KRel.allProj {Γ : Ctx} (m : Mask) :
    KRel I (Ctx.tupConv N I (Γ.sub m)) (KS.all (Ctx.projS N Γ m)) (K.all (Ctx.proj Γ m)) :=
  fun ρ => ⟨Ctx.tupConv_projS I Γ m ρ, Ctx.tupConv_projS I Γ m ρ, Ctx.tupConv_projS I Γ m ρ⟩

/-- The states of a loop or branch relate through `Ctx.tupConv`. -/
theorem projS_rel {Γ : Ctx} (m : Mask) (ρ : Γ.denS N) :
    Ctx.tupConv N I (Γ.sub m) (Ctx.projS N Γ m ρ) = Ctx.proj Γ m (Ctx.conv N I Γ ρ) := Ctx.tupConv_projS I Γ m ρ

mutual
  theorem TStmts.denoteRS_conv : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) {RS RC : Type} (h : RS → RC)
      (rS : τ.den N → RS) (rC : τ.denote → RC), (∀ v, h (rS v) = rC (Ty.conv N I τ v)) →
      ∀ (kS : KS N Γ RS) (kC : K Γ RC), KRel I h kS kC → ∀ (ρ : Γ.denS N),
      h (TStmts.denoteRS N I fs rS st kS ρ) = st.denoteR (Sigs.canon N I Φ fs) rC kC (Ctx.conv N I Γ ρ)
    | _, _, .nil, _, _, _, _, _, _, _, _, hk, ρ => (hk ρ).1
    | _, _, .brk _, _, _, _, _, _, _, _, _, hk, ρ => (hk ρ).2.1
    | _, _, .cont _, _, _, _, _, _, _, _, _, hk, ρ => (hk ρ).2.2
    | _, _, .ret e _, _, _, _, _, _, hr, _, _, _, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]; rw [hr, TExpr.conv_denS I fs e ρ]
    | _, _, .retVoid v _, _, _, _, _, _, hr, _, _, _, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]; rw [hr, Var.conv_getS I v ρ]
    | _, _, .const _ e rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr _ _ (KRel.snd I hk), ← TExpr.conv_denS I fs e ρ]; rfl
    | _, _, .let_ _ e rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr _ _ (KRel.snd I hk), ← TExpr.conv_denS I fs e ρ]; rfl
    | _, _, .assign v e rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Var.conv_setS, TExpr.conv_denS I fs e ρ]
    | _, _, .stateSet v i _ key e rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Var.conv_setS, recSet_conv, Var.conv_getS]
      have hk' : TExpr.denS N I fs key ρ = _ := TExpr.conv_denS I fs key ρ
      rw [Ty.conv_mapPut, recGet_conv, Var.conv_getS, TExpr.conv_denS I fs e ρ, hk']
    | _, _, .stateDelete v i _ key rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Var.conv_setS, recSet_conv, Var.conv_getS]
      have hk' : TExpr.denS N I fs key ρ = _ := TExpr.conv_denS I fs key ρ
      rw [Ty.conv_mapDel, recGet_conv, Var.conv_getS, hk']
    | _, _, .callVoid fn v args rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Var.conv_setS]
      congr 2
      refine (FVar.conv_getS I fn fs _).trans ?_
      show fn.get _ (Ty.conv N I _ (Var.getS N v ρ), Ctx.conv N I _ (TArgs.denS N I fs args ρ)) = _
      rw [Var.conv_getS, TArgs.conv_denS I fs args ρ]
    | _, _, .block body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      exact TStmts.denoteRS_conv body h rS rC hr _ _
        (KRel.normal I (TStmts.denoteRS_conv rest h rS rC hr kS kC hk) hk) ρ
    | _, _, .ite c yes no rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hc : TExpr.denS N I fs c ρ = _ := TExpr.conv_denS I fs c ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, hc]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
        congr 2
        split
        · exact TStmts.denoteRS_conv yes _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _ (KRel.allProj I (Mask.or yes.writes no.writes)) ρ
        · exact TStmts.denoteRS_conv no _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _ (KRel.allProj I (Mask.or yes.writes no.writes)) ρ
      · have hk' := KRel.normal I (TStmts.denoteRS_conv rest h rS rC hr kS kC hk) hk
        split
        · exact TStmts.denoteRS_conv yes h rS rC hr _ _ hk' ρ
        · exact TStmts.denoteRS_conv no h rS rC hr _ _ hk' ρ
    | _, _, .ifNull v _ yes no rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.denoteRS, TStmts.denoteR]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS, ← hv]
        congr 2
        rcases Var.getS N v ρ with _ | y
        · exact TStmts.denoteRS_conv yes _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _ (KRel.allProj I (Mask.or yes.writes no.writes)) ρ
        · show _ = no.denoteR _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
          rw [← Var.conv_narrowValS]
          exact TStmts.denoteRS_conv no _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _
            (KRel.widen I v (KRel.allProj I (Mask.or yes.writes no.writes))) _
      · have hk' := KRel.normal I (TStmts.denoteRS_conv rest h rS rC hr kS kC hk) hk
        rw [← hv]
        rcases Var.getS N v ρ with _ | y
        · exact TStmts.denoteRS_conv yes h rS rC hr _ _ hk' ρ
        · show _ = no.denoteR _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
          rw [← Var.conv_narrowValS]
          exact TStmts.denoteRS_conv no h rS rC hr _ _ (KRel.widen I v hk') _
    | _, _, .ifNotNull v _ yes no rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.denoteRS, TStmts.denoteR]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS, ← hv]
        congr 2
        rcases Var.getS N v ρ with _ | y
        · exact TStmts.denoteRS_conv no _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _ (KRel.allProj I (Mask.or yes.writes no.writes)) ρ
        · show _ = yes.denoteR _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
          rw [← Var.conv_narrowValS]
          exact TStmts.denoteRS_conv yes _ _ _ (fun _ => projS_rel I (Mask.or yes.writes no.writes) ρ) _ _
            (KRel.widen I v (KRel.allProj I (Mask.or yes.writes no.writes))) _
      · have hk' := KRel.normal I (TStmts.denoteRS_conv rest h rS rC hr kS kC hk) hk
        rw [← hv]
        rcases Var.getS N v ρ with _ | y
        · exact TStmts.denoteRS_conv no h rS rC hr _ _ hk' ρ
        · show _ = yes.denoteR _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
          rw [← Var.conv_narrowValS]
          exact TStmts.denoteRS_conv yes h rS rC hr _ _ (KRel.widen I v hk') _
    | _, _, .ifNullExit v _ yes rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, ← hv]
      rcases Var.getS N v ρ with _ | y
      · exact TStmts.denoteRS_conv yes h rS rC hr kS kC hk ρ
      · show _ = rest.denoteR _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS]
        exact TStmts.denoteRS_conv rest h rS rC hr _ _ (KRel.widen I v hk) _
    | _, _, .switchG v _ arms rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, ← hv, Ty.conv_union, Variants.elim_conv, unionElim_eq]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
        congr 2
        rw [Variants.elimS_nat (Ctx.tupConv N I _)]
        refine Variants.elimS_congr _ _ _ _ fun i y => ?_
        exact TArms.denoteRS_conv arms _ _ _ (fun _ => projS_rel I arms.writes ρ) _ _
          (KRel.allProj I arms.writes) ρ i y _ _ (projS_rel I arms.writes ρ)
      · rw [Variants.elimS_nat h]
        refine Variants.elimS_congr _ _ _ _ fun i y => ?_
        have hrest := TStmts.denoteRS_conv rest h rS rC hr kS kC hk
        exact TArms.denoteRS_conv arms h rS rC hr
          { kS with normal := TStmts.denoteRS N I fs rS rest kS, brk := TStmts.denoteRS N I fs rS rest kS }
          { kC with normal := rest.denoteR (Sigs.canon N I Φ fs) rC kC, brk := rest.denoteR (Sigs.canon N I Φ fs) rC kC }
          (fun ρ' => ⟨hrest ρ', hrest ρ', (hk ρ').2.2⟩) ρ i y _ _ (hrest ρ)
    | _, _, .forOf _ a body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have ha := TExpr.conv_denS I fs a ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, ← ha]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
        congr 2
        show _ = List.foldl _ _ (List.map _ _)
        rw [foldl_conv (Ty.conv N I _) (Ctx.tupConv N I _) _ _ (fun s y => ?_), projS_rel]
        exact (TStmts.denoteRS_conv body (Ctx.tupConv N I _) (fun _ => s) (fun _ => Ctx.tupConv N I _ s) (fun _ => rfl)
          (KS.map Prod.snd (KS.all (Ctx.projS N _ body.writes.tail)))
          (K.map Prod.snd (K.all (Ctx.proj _ body.writes.tail))) (KRel.snd I (KRel.allProj I body.writes.tail)) _).trans
          (by simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl)
      · show _ = forIn (List.map _ _) _ _ _
        rw [← projS_rel]
        refine forIn_conv _ _ h _ _ (fun y nS eS nC eC s hn he => ?_) _ _ (fun s => ?_) _ _
        · refine (TStmts.denoteRS_conv body h rS rC hr _ (K.map Prod.snd ⟨nC ∘ Ctx.proj _ body.writes.tail,
            eC ∘ Ctx.proj _ body.writes.tail, nC ∘ Ctx.proj _ body.writes.tail⟩) (KRel.snd I (fun ρ' => ?_)) _).trans ?_
          · simp only [Function.comp]; rw [hn, he, projS_rel]; exact ⟨rfl, rfl, rfl⟩
          · simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl
        · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
    | _, _, .forEntries _ _ a body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have ha := TExpr.conv_denS I fs a ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, ← ha]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
        congr 2
        show _ = List.foldl _ _ (List.zipIdx (List.map _ _))
        rw [List.zipIdx_map, foldl_conv (Prod.map (Ty.conv N I _) id) (Ctx.tupConv N I _) _ _ (fun s p => ?_), projS_rel]
        exact (TStmts.denoteRS_conv body (Ctx.tupConv N I _) (fun _ => s) (fun _ => Ctx.tupConv N I _ s) (fun _ => rfl)
          (KS.map Prod.snd (KS.map Prod.snd (KS.all (Ctx.projS N _ body.writes.tail.tail))))
          (K.map Prod.snd (K.map Prod.snd (K.all (Ctx.proj _ body.writes.tail.tail))))
          (KRel.snd I (KRel.snd I (KRel.allProj I body.writes.tail.tail))) _).trans
          (by simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl)
      · show _ = forIn (List.zipIdx (List.map _ _)) _ _ _
        rw [List.zipIdx_map, ← projS_rel]
        refine forIn_conv _ _ h _ _ (fun p nS eS nC eC s hn he => ?_) _ _ (fun s => ?_) _ _
        · refine (TStmts.denoteRS_conv body h rS rC hr _ (K.map Prod.snd (K.map Prod.snd
            ⟨nC ∘ Ctx.proj _ body.writes.tail.tail, eC ∘ Ctx.proj _ body.writes.tail.tail,
              nC ∘ Ctx.proj _ body.writes.tail.tail⟩)) (KRel.snd I (KRel.snd I (fun ρ' => ?_))) _).trans ?_
          · simp only [Function.comp]; rw [hn, he, projS_rel]; exact ⟨rfl, rfl, rfl⟩
          · simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl
        · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
    | _, _, .forRange _ v body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      have hv : Var.getS N v ρ = _ := Var.conv_getS I v ρ
      simp only [TStmts.denoteRS, TStmts.denoteR, hv]
      split
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
        congr 2
        conv => rhs; rw [← List.map_id (range _)]
        rw [foldl_conv id (Ctx.tupConv N I _) _ _ (fun s j => ?_), projS_rel]
        exact (TStmts.denoteRS_conv body (Ctx.tupConv N I _) (fun _ => s) (fun _ => Ctx.tupConv N I _ s) (fun _ => rfl)
          (KS.map Prod.snd (KS.all (Ctx.projS N _ body.writes.tail)))
          (K.map Prod.snd (K.all (Ctx.proj _ body.writes.tail))) (KRel.snd I (KRel.allProj I body.writes.tail)) _).trans
          (by simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl)
      · conv => rhs; rw [← List.map_id (range _)]
        rw [← projS_rel]
        refine forIn_conv _ _ h _ _ (fun j nS eS nC eC s hn he => ?_) _ _ (fun s => ?_) _ _
        · refine (TStmts.denoteRS_conv body h rS rC hr _ (K.map Prod.snd ⟨nC ∘ Ctx.proj _ body.writes.tail,
            eC ∘ Ctx.proj _ body.writes.tail, nC ∘ Ctx.proj _ body.writes.tail⟩) (KRel.snd I (fun ρ' => ?_)) _).trans ?_
          · simp only [Function.comp]; rw [hn, he, projS_rel]; exact ⟨rfl, rfl, rfl⟩
          · simp only [Ctx.conv, Ctx.conv_mergeS] <;> rfl
        · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
    | _, _, .whileLoop c body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => by
      simp only [TStmts.denoteRS, TStmts.denoteR]
      rw [whileDo_def, whileDo_def, ← projS_rel]
      refine whileIn_conv _ h _ _ (fun s => ?_) _ _ (fun nS eS nC eC s hn he => ?_) _ _ _ _ (fun s => ?_) (fun s => ?_) _ _
      · have hc : TExpr.denS N I fs c _ = _ := TExpr.conv_denS I fs c (Ctx.mergeS N _ body.writes ρ s)
        rw [hc, Ctx.conv_mergeS]
      · refine (TStmts.denoteRS_conv body h rS rC hr _ ⟨nC ∘ Ctx.proj _ body.writes, eC ∘ Ctx.proj _ body.writes,
          nC ∘ Ctx.proj _ body.writes⟩ (fun ρ' => ?_) _).trans ?_
        · simp only [Function.comp]; rw [hn, he, projS_rel]; exact ⟨rfl, rfl, rfl⟩
        · rw [Ctx.conv_mergeS]
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]
      · rw [TStmts.denoteRS_conv rest h rS rC hr kS kC hk, Ctx.conv_mergeS]

  theorem TArms.firstRS_conv {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {RS RC : Type} (h : RS → RC) (rS : τ.den N → RS) (rC : τ.denote → RC),
      (∀ v, h (rS v) = rC (Ty.conv N I τ v)) → ∀ (kS : KS N Γ RS) (kC : K Γ RC), KRel I h kS kC → ∀ (ρ : Γ.denS N),
      h (TArms.firstRS N I fs rS arms kS ρ) = arms.firstR (Sigs.canon N I Φ fs) rC kC (Ctx.conv N I Γ ρ)
    | .nil, _, _, _, _, _, _, _, _, hk, ρ => (hk ρ).1
    | .empty _ rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ => TArms.firstRS_conv rest h rS rC hr kS kC hk ρ
    | .wide _ body _, _, _, h, rS, rC, hr, kS, kC, hk, ρ => TStmts.denoteRS_conv body h rS rC hr kS kC hk ρ
    | .narrow .., _, _, _, _, _, _, _, _, hk, ρ => (hk ρ).1

  theorem TArms.denoteRS_conv {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) {RS RC : Type} (h : RS → RC) (rS : τ.den N → RS) (rC : τ.denote → RC),
      (∀ v, h (rS v) = rC (Ty.conv N I τ v)) → ∀ (kS : KS N Γ RS) (kC : K Γ RC), KRel I h kS kC → ∀ (ρ : Γ.denS N)
      {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.den N) (dS : RS) (dC : RC), h dS = dC →
      h (TArms.denoteRS N I fs rS arms kS ρ i y dS) =
        arms.denoteR (Sigs.canon N I Φ fs) rC kC (Ctx.conv N I Γ ρ) i (Fields.conv N I fds y) dC
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.denoteRS, TArms.denoteR]
      split
      · exact TArms.firstRS_conv rest h rS rC hr kS kC hk ρ
      · refine TArms.denoteRS_conv rest h rS rC hr kS kC hk ρ i y _ _ ?_
        split
        · exact TArms.firstRS_conv rest h rS rC hr kS kC hk ρ
        · exact hd
    | .wide l body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.denoteRS, TArms.denoteR]
      split
      · exact TStmts.denoteRS_conv body h rS rC hr kS kC hk ρ
      · refine TArms.denoteRS_conv rest h rS rC hr kS kC hk ρ i y _ _ ?_
        split
        · exact TStmts.denoteRS_conv body h rS rC hr kS kC hk ρ
        · exact hd
    | .narrow i' body rest, _, _, h, rS, rC, hr, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.denoteRS, TArms.denoteR]
      rw [← Variants.conv_injS I i y, VIdx.proj_conv]
      rcases VIdx.projS N i' (VIdx.injS N i y) with _ | y'
      · exact TArms.denoteRS_conv rest h rS rC hr kS kC hk ρ i y dS dC hd
      · show _ = body.denoteR _ rC _ (v.narrowVal _ ((), Fields.conv N I _ y'))
        have hn : ((), Fields.conv N I _ y') = Ty.conv N I _ (vrecOf N I key i' y') :=
          (Ty.conv_recMk I (.cons key (.tag _) _) ((), y')).symm
        rw [hn, ← Var.conv_narrowValS]
        exact TStmts.denoteRS_conv body h rS rC hr _ _
          (KRel.map I _ _ (Var.conv_widenS I v _ _ (fun z => by rw [Narrowing.conv_embedS]; rfl)) hk) _
end

end

/-! ## Safety of statements -/

section
variable {N : Names} (I : Isos N) {Φ : Sigs} (fs : Φ.denS N) (ss : Φ.safetyS N)

set_option maxRecDepth 8192 in
mutual
  theorem TStmts.safeS_eq : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (kS : KS N Γ Bool) (kC : K Γ Bool),
      KRel I id kS kC → ∀ (ρ : Γ.denS N),
      TStmts.safeS N I fs ss st kS ρ = st.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) kC (Ctx.conv N I Γ ρ)
    | _, _, .nil, _, _, hk, ρ => (hk ρ).1
    | _, _, .brk _, _, _, hk, ρ => (hk ρ).2.1
    | _, _, .cont _, _, _, hk, ρ => (hk ρ).2.2
    | _, _, .retVoid _ _, _, _, _, _ => rfl
    | _, _, .ret e _, _, _, _, ρ => by
      simp only [TStmts.safeS, TStmts.safe]; rw [TExpr.safeS_eq I fs ss e ρ]
    | _, _, .const _ e rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      rw [TExpr.safeS_eq I fs ss e ρ, TStmts.safeS_eq rest _ _ (KRel.snd I hk), ← TExpr.conv_denS I fs e ρ]; rfl
    | _, _, .let_ _ e rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      rw [TExpr.safeS_eq I fs ss e ρ, TStmts.safeS_eq rest _ _ (KRel.snd I hk), ← TExpr.conv_denS I fs e ρ]; rfl
    | _, _, .assign v e rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      rw [TExpr.safeS_eq I fs ss e ρ, TStmts.safeS_eq rest kS kC hk, Var.conv_setS, TExpr.conv_denS I fs e ρ]
    | _, _, .stateSet v i _ key e rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      have hk' : TExpr.denS N I fs key ρ = _ := TExpr.conv_denS I fs key ρ
      rw [TExpr.safeS_eq I fs ss key ρ, TExpr.safeS_eq I fs ss e ρ, TStmts.safeS_eq rest kS kC hk, Var.conv_setS,
        recSet_conv, Var.conv_getS, Ty.conv_mapPut, recGet_conv, Var.conv_getS, TExpr.conv_denS I fs e ρ, hk']
    | _, _, .stateDelete v i _ key rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      have hk' : TExpr.denS N I fs key ρ = _ := TExpr.conv_denS I fs key ρ
      rw [TExpr.safeS_eq I fs ss key ρ, TStmts.safeS_eq rest kS kC hk, Var.conv_setS, recSet_conv, Var.conv_getS,
        Ty.conv_mapDel, recGet_conv, Var.conv_getS, hk']
    | _, _, .callVoid fn v args rest, kS, kC, hk, ρ => by
      have e1 : Ty.conv N I _ (FVar.getS N fn fs (Var.getS N v ρ, TArgs.denS N I fs args ρ)) =
          fn.get (Sigs.canon N I Φ fs) (v.get (Ctx.conv N I _ ρ), args.denote (Sigs.canon N I Φ fs) (Ctx.conv N I _ ρ)) := by
        refine (FVar.conv_getS I fn fs _).trans ?_
        show fn.get _ (Ty.conv N I _ (Var.getS N v ρ), Ctx.conv N I _ (TArgs.denS N I fs args ρ)) = _
        rw [Var.conv_getS, TArgs.conv_denS I fs args ρ]
      simp only [TStmts.safeS, TStmts.safe]
      rw [TArgs.safeS_eq I fs ss args ρ, TStmts.safeS_eq rest kS kC hk, Var.conv_setS, FVar.safeS_eq I, e1]
      simp only [Ctx.conv]
      rw [Var.conv_getS, TArgs.conv_denS I fs args ρ]
    | _, _, .block body rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      exact TStmts.safeS_eq body _ _ (KRel.normal (h := id) I (TStmts.safeS_eq rest kS kC hk) hk) ρ
    | _, _, .ite c yes no rest, kS, kC, hk, ρ => by
      have hc : TExpr.denS N I fs c ρ = _ := TExpr.conv_denS I fs c ρ
      simp only [TStmts.safeS, TStmts.safe, hc, TExpr.safeS_eq I fs ss c ρ]
      have hk' := KRel.normal (h := id) I (TStmts.safeS_eq rest kS kC hk) hk
      split
      · rw [TStmts.safeS_eq yes _ _ hk' ρ]
      · rw [TStmts.safeS_eq no _ _ hk' ρ]
    | _, _, .ifNull v _ yes no rest, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.safeS, TStmts.safe, ← hv]
      have hk' := KRel.normal (h := id) I (TStmts.safeS_eq rest kS kC hk) hk
      rcases Var.getS N v ρ with _ | y
      · exact TStmts.safeS_eq yes _ _ hk' ρ
      · show _ = no.safe _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS]
        exact TStmts.safeS_eq no _ _ (KRel.widen I v hk') _
    | _, _, .ifNotNull v _ yes no rest, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.safeS, TStmts.safe, ← hv]
      have hk' := KRel.normal (h := id) I (TStmts.safeS_eq rest kS kC hk) hk
      rcases Var.getS N v ρ with _ | y
      · exact TStmts.safeS_eq no _ _ hk' ρ
      · show _ = yes.safe _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS]
        exact TStmts.safeS_eq yes _ _ (KRel.widen I v hk') _
    | _, _, .ifNullExit v _ yes rest, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.safeS, TStmts.safe, ← hv]
      rcases Var.getS N v ρ with _ | y
      · exact TStmts.safeS_eq yes kS kC hk ρ
      · show _ = rest.safe _ _ _ (v.narrowVal _ (Ty.conv N I _ y))
        rw [← Var.conv_narrowValS]
        exact TStmts.safeS_eq rest _ _ (KRel.widen I v hk) _
    | _, _, .switchG v _ arms rest, kS, kC, hk, ρ => by
      have hv := Var.conv_getS I v ρ
      simp only [TStmts.safeS, TStmts.safe, ← hv, Ty.conv_union, Variants.elim_conv, unionElim_eq]
      refine Variants.elimS_congr _ _ _ _ fun i y => ?_
      have hrest := TStmts.safeS_eq rest kS kC hk
      exact TArms.safeS_eq arms
        { kS with normal := TStmts.safeS N I fs ss rest kS, brk := TStmts.safeS N I fs ss rest kS }
        { kC with normal := rest.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) kC,
                  brk := rest.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) kC }
        (fun ρ' => ⟨hrest ρ', hrest ρ', (hk ρ').2.2⟩) ρ i y _ _ (hrest ρ)
    | _, _, .forOf _ a body rest, kS, kC, hk, ρ => by
      have ha := TExpr.conv_denS I fs a ρ
      simp only [TStmts.safeS, TStmts.safe, ← ha, TExpr.safeS_eq I fs ss a ρ]
      congr 1
      show _ = forIn (List.map _ _) _ _ _
      refine forIn_conv _ (Ctx.conv N I _) id _ _ (fun y nS eS nC eC s hn he => ?_) _ _
        (fun s => TStmts.safeS_eq rest kS kC hk s) _ _
      exact TStmts.safeS_eq body _ (K.map Prod.snd ⟨nC, eC, nC⟩)
        (KRel.snd I (fun ρ' => ⟨hn ρ', he ρ', hn ρ'⟩)) _
    | _, _, .forEntries _ _ a body rest, kS, kC, hk, ρ => by
      have ha := TExpr.conv_denS I fs a ρ
      simp only [TStmts.safeS, TStmts.safe, ← ha, TExpr.safeS_eq I fs ss a ρ]
      congr 1
      show _ = forIn (List.zipIdx (List.map _ _)) _ _ _
      rw [List.zipIdx_map]
      refine forIn_conv _ (Ctx.conv N I _) id _ _ (fun p nS eS nC eC s hn he => ?_) _ _
        (fun s => TStmts.safeS_eq rest kS kC hk s) _ _
      exact TStmts.safeS_eq body _ (K.map Prod.snd (K.map Prod.snd ⟨nC, eC, nC⟩))
        (KRel.snd I (KRel.snd I (fun ρ' => ⟨hn ρ', he ρ', hn ρ'⟩))) _
    | _, _, .forRange _ v body rest, kS, kC, hk, ρ => by
      have hv : Var.getS N v ρ = _ := Var.conv_getS I v ρ
      simp only [TStmts.safeS, TStmts.safe, hv]
      conv => rhs; rw [← List.map_id (range _)]
      refine forIn_conv _ (Ctx.conv N I _) id _ _ (fun j nS eS nC eC s hn he => ?_) _ _
        (fun s => TStmts.safeS_eq rest kS kC hk s) _ _
      exact TStmts.safeS_eq body _ (K.map Prod.snd ⟨nC, eC, nC⟩)
        (KRel.snd I (fun ρ' => ⟨hn ρ', he ρ', hn ρ'⟩)) _
    | _, _, .whileLoop c body rest, kS, kC, hk, ρ => by
      simp only [TStmts.safeS, TStmts.safe]
      rw [whileSafe_def, whileSafe_def]
      refine whileIn_conv (Ctx.conv N I _) id _ _ (fun s => ?_) _ _
        (fun nS eS nC eC s hn he => ?_) _ _ _ _ (fun s => TStmts.safeS_eq rest kS kC hk s) (fun _ => rfl) _ _
      · have hc : TExpr.denS N I fs c s = _ := TExpr.conv_denS I fs c s
        exact hc
      · exact TStmts.safeS_eq body _ ⟨nC, eC, nC⟩ (fun ρ' => ⟨hn ρ', he ρ', hn ρ'⟩) _

  theorem TArms.firstSafeS_eq {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (kS : KS N Γ Bool) (kC : K Γ Bool), KRel I id kS kC → ∀ (ρ : Γ.denS N),
      TArms.firstSafeS N I fs ss arms kS ρ =
        arms.firstSafe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) kC (Ctx.conv N I Γ ρ)
    | .nil, _, _, hk, ρ => (hk ρ).1
    | .empty _ rest, kS, kC, hk, ρ => TArms.firstSafeS_eq rest kS kC hk ρ
    | .wide _ body _, kS, kC, hk, ρ => TStmts.safeS_eq body kS kC hk ρ
    | .narrow .., _, _, hk, ρ => (hk ρ).1

  theorem TArms.safeS_eq {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      ∀ (arms : TArms Φ Γ τ v) (kS : KS N Γ Bool) (kC : K Γ Bool), KRel I id kS kC → ∀ (ρ : Γ.denS N)
      {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.den N) (dS dC : Bool), dS = dC →
      TArms.safeS N I fs ss arms kS ρ i y dS =
        arms.safe (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) kC (Ctx.conv N I Γ ρ) i (Fields.conv N I fds y) dC
    | .nil, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.safeS, TArms.safe]
      split
      · exact TArms.firstSafeS_eq rest kS kC hk ρ
      · refine TArms.safeS_eq rest kS kC hk ρ i y _ _ ?_
        split
        · exact TArms.firstSafeS_eq rest kS kC hk ρ
        · exact hd
    | .wide l body rest, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.safeS, TArms.safe]
      split
      · exact TStmts.safeS_eq body kS kC hk ρ
      · refine TArms.safeS_eq rest kS kC hk ρ i y _ _ ?_
        split
        · exact TStmts.safeS_eq body kS kC hk ρ
        · exact hd
    | .narrow i' body rest, kS, kC, hk, ρ, t, _, i, y, dS, dC, hd => by
      simp only [TArms.safeS, TArms.safe]
      rw [← Variants.conv_injS I i y, VIdx.proj_conv]
      rcases VIdx.projS N i' (VIdx.injS N i y) with _ | y'
      · exact TArms.safeS_eq rest kS kC hk ρ i y dS dC hd
      · show _ = body.safe _ _ _ (v.narrowVal _ ((), Fields.conv N I _ y'))
        have hn : ((), Fields.conv N I _ y') = Ty.conv N I _ (vrecOf N I key i' y') :=
          (Ty.conv_recMk I (.cons key (.tag _) _) ((), y')).symm
        rw [hn, ← Var.conv_narrowValS]
        exact TStmts.safeS_eq body _ _
          (KRel.map I _ _ (Var.conv_widenS I v _ _ (fun z => by rw [Narrowing.conv_embedS]; rfl)) hk) _
end

end

/-! ## Representation of the program's values -/

section
variable (N : Names) (I : Isos N)

mutual
  /-- `Ty.Rep` over the program's types: the JavaScript value `v` represents `x`. On a type with no
  named record or union inside it, it unfolds to `Ty.Rep`'s cases. -/
  def Ty.RepS : (τ : Ty) → JSValue → τ.den N → Prop
    | .bool, v, b => v = .bool b
    | .int, v, n => v = .bigint n
    | .number, v, n => v = .number n
    | .string, v, s => v = .string s
    | .tag t, v, _ => v = t.value
    | .lits a as, v, i => v = .string ((a :: as)[i])
    | .option n _, v, none => n.admits v
    | .option _ τ, v, some x => Ty.RepS τ v x
    | .record fs, v, x => ∃ kvs, v = .record kvs ∧ (kvs.map Prod.fst).Nodup ∧ Fields.RepS fs kvs (recView N I fs x)
    | .union key vs, v, x =>
      ∃ kvs, v = .record kvs ∧ (kvs.map Prod.fst).Nodup ∧ Variants.RepS key vs kvs (unionView N I vs x)
    | .array τ, v, xs => ∃ vs, v = .array vs ∧ Forall2 (fun w x => Ty.RepS τ w x) vs xs
    | .map τ, v, m => ∃ kvs, v = .map kvs ∧ Forall2 (fun p q => p.1 = q.1 ∧ Ty.RepS τ p.2 q.2) kvs m

  def Fields.RepS : (fs : Fields) → List (String × JSValue) → fs.den N → Prop
    | .nil, _, _ => True
    | .cons f τ rest, kvs, (x, xs) => Ty.RepS τ (fieldOf kvs f) x ∧ Fields.RepS rest kvs xs

  def Variants.RepS (key : String) : (vs : Variants) → List (String × JSValue) → vs.den N → Prop
    | .one t fs, kvs, x => fieldOf kvs key = t.value ∧ Fields.RepS fs kvs x
    | .cons t fs _, kvs, .inl x => fieldOf kvs key = t.value ∧ Fields.RepS fs kvs x
    | .cons _ _ rest, kvs, .inr y => Variants.RepS key rest kvs y
end

/-- `EnvRel` over the program's types. -/
def EnvRelS : (Γ : Ctx) → Env → Γ.denS N → Prop
  | [], env, _ => env = []
  | (x, τ) :: Γ, env, (a, ρ) => ∃ w env', env = (x, w) :: env' ∧ Ty.RepS N I τ w a ∧ EnvRelS Γ env' ρ

/-- `ArgsRep` over the program's types: the arguments `vs` represent the inputs `xs`. -/
def ArgsRepS (ps : Ctx) (vs : List JSValue) (xs : ps.denS N) : Prop :=
  EnvRelS N I ps (bindParams (ps.map Prod.fst) vs) xs

theorem forall2_map {α β γ : Type} (R : α → γ → Prop) (f : β → γ) :
    ∀ (as : List α) (bs : List β), Forall2 R as (bs.map f) = Forall2 (fun a b => R a (f b)) as bs
  | [], [] => propext ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => propext ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | _ :: _, [] => propext ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | a :: as, b :: bs => by
    rw [List.map_cons]
    apply propext
    constructor
    · intro h; cases h with | cons h1 h2 => exact .cons h1 (forall2_map R f as bs ▸ h2)
    · intro h; cases h with | cons h1 h2 => exact .cons h1 ((forall2_map R f as bs).symm ▸ h2)

mutual
  theorem Ty.repS_eq : ∀ (τ : Ty) (v : JSValue) (x : τ.den N), Ty.RepS N I τ v x = τ.Rep v (Ty.conv N I τ x)
    | .bool, _, _ | .int, _, _ | .number, _, _ | .string, _, _ | .tag _, _, _ | .lits _ _, _, _ => rfl
    | .option _ _, _, none => rfl
    | .option _ τ, v, some x => Ty.repS_eq τ v x
    | .record fs, v, x => by
      simp only [Ty.RepS, Ty.Rep, Ty.conv_record, Fields.repS_eq fs]
    | .union key vs, v, x => by
      simp only [Ty.RepS, Ty.Rep, Ty.conv_union, Variants.repS_eq key vs]
    | .array τ, v, xs => by
      simp only [Ty.RepS, Ty.Rep, Ty.conv, forall2_map, Ty.repS_eq τ]
    | .map τ, v, m => by
      simp only [Ty.RepS, Ty.Rep, Ty.conv, forall2_map, Ty.repS_eq τ]

  theorem Fields.repS_eq : ∀ (fs : Fields) (kvs : List (String × JSValue)) (x : fs.den N),
      Fields.RepS N I fs kvs x = fs.Rep kvs (Fields.conv N I fs x)
    | .nil, _, _ => rfl
    | .cons _ τ rest, kvs, (x, xs) => by
      simp only [Fields.RepS, Fields.Rep, Fields.conv, Ty.repS_eq τ, Fields.repS_eq rest]

  theorem Variants.repS_eq (key : String) : ∀ (vs : Variants) (kvs : List (String × JSValue)) (x : vs.den N),
      Variants.RepS N I key vs kvs x = vs.Rep key kvs (Variants.conv N I vs x)
    | .one _ fs, kvs, x => by simp only [Variants.RepS, Variants.Rep, Variants.conv, Fields.repS_eq fs]
    | .cons _ fs _, kvs, .inl x => by simp only [Variants.RepS, Variants.Rep, Variants.conv, Fields.repS_eq fs]
    | .cons _ _ rest, kvs, .inr y => by
      simp only [Variants.RepS, Variants.Rep, Variants.conv, Variants.repS_eq key rest]
end

theorem EnvRelS_eq : ∀ (Γ : Ctx) (env : Env) (ρ : Γ.denS N), EnvRelS N I Γ env ρ = EnvRel Γ env (Ctx.conv N I Γ ρ)
  | [], _, _ => rfl
  | (_, τ) :: Γ, env, (a, ρ) => by
    simp only [EnvRelS, EnvRel, Ctx.conv, Ty.repS_eq, EnvRelS_eq Γ]

theorem ArgsRepS_eq (ps : Ctx) (vs : List JSValue) (xs : ps.denS N) :
    ArgsRepS N I ps vs xs = ArgsRep ps vs (Ctx.conv N I ps xs) :=
  EnvRelS_eq N I ps _ xs

end

/-! ## Functions, programs, and what a generated file concludes -/

section
variable {N : Names} (I : Isos N)

/-- **The denotation over named types is the denotation**: a function body's `denoteFn`, on the
denotation's values, is its `denoteRSFn` on the converted values, converted back. -/
theorem TStmts.denoteFn_eq_S {Φ : Sigs} {Γ : Ctx} {τ : Ty} (body : TStmts Φ Γ τ) (fs : Φ.denS N) :
    body.denoteFn (Sigs.canon N I Φ fs) = fun c => Ty.conv N I τ (body.denoteRSFn N I fs (Ctx.convInv N I Γ c)) := by
  rw [TStmts.denoteFn_eq_R]
  funext c
  conv => lhs; rw [← Ctx.conv_convInv I Γ c]
  exact (TStmts.denoteRS_conv I fs body (Ty.conv N I τ) id id (fun _ => rfl) _ _
    (KRel.all I fun _ => Ty.conv_defaultS I τ) (Ctx.convInv N I Γ c)).symm

theorem TStmts.safeFn_eq_S {Φ : Sigs} {Γ : Ctx} {τ : Ty} (body : TStmts Φ Γ τ) (fs : Φ.denS N) (ss : Φ.safetyS N) :
    body.safeFn (Sigs.canon N I Φ fs) (Sigs.canonSafety N I Φ ss) = fun c => body.safeFnS N I fs ss (Ctx.convInv N I Γ c) := by
  funext c
  simp only [TStmts.safeFn, TStmts.safeFnS]
  split
  · rfl
  · conv => lhs; rw [← Ctx.conv_convInv I Γ c]
    exact (TStmts.safeS_eq I fs ss body _ _ (KRel.all I fun _ => rfl) (Ctx.convInv N I Γ c)).symm

/-- Assemble a program's denotation from per-function equations over named types. -/
theorem TProgram.denote_consS {Φ : Sigs} {s : Sig} {body : TStmts Φ s.params s.result} {P : TProgram Φ}
    {fs : Φ.denS N} {g : s.denS N} (hP : P.denote = Sigs.canon N I Φ fs) (hg : body.denoteRSFn N I fs = g) :
    (TProgram.cons s body P).denote = Sigs.canon N I (s :: Φ) (g, fs) := by
  rw [TProgram.denote, hP, TStmts.denoteFn_eq_S I body fs, hg]; rfl

theorem TProgram.safety_consS {Φ : Sigs} {s : Sig} {body : TStmts Φ s.params s.result} {P : TProgram Φ}
    {fs : Φ.denS N} {ss : Φ.safetyS N} {g : s.params.denS N → Bool} (hP : P.denote = Sigs.canon N I Φ fs)
    (hS : P.safety = Sigs.canonSafety N I Φ ss) (hg : body.safeFnS N I fs ss = g) :
    (TProgram.cons s body P).safety = Sigs.canonSafety N I (s :: Φ) (g, ss) := by
  rw [TProgram.safety, hP, hS, TStmts.safeFn_eq_S I body fs ss, hg]; rfl

/-- Adequacy for a file whose readable definitions use named types: every run on arguments representing
the inputs converges to a value representing the readable definition's result. -/
theorem source_ofS {Φ : Sigs} {P : TProgram Φ} {ast : Program} {fs : Φ.denS N} {ss : Φ.safetyS N}
    (erased : P.erase = ast) (wf : P.WF) (denote_eq : P.denote = Sigs.canon N I Φ fs)
    (safety_eq : P.safety = Sigs.canonSafety N I Φ ss) {f : String} {s : Sig} (v : FVar Φ f s) (hv : s.void = false)
    (xs : s.params.denS N) (vs : List JSValue) (args : ArgsRepS N I s.params vs xs)
    (safe : FVar.safeS N v ss xs = true) :
    ∃ w, Converges (fun n => run ast n f vs) (.ok w) ∧ Ty.RepS N I s.result w (FVar.getS N v fs xs) := by
  rw [ArgsRepS_eq] at args
  obtain ⟨w, hc, hr⟩ := source_of erased wf denote_eq safety_eq v hv _ vs args (by rw [← FVar.safeS_eq I]; exact safe)
  exact ⟨w, hc, by rw [Ty.repS_eq, FVar.conv_getS]; exact hr⟩

theorem source_state_ofS {Φ : Sigs} {P : TProgram Φ} {ast : Program} {fs : Φ.denS N} {ss : Φ.safetyS N}
    (erased : P.erase = ast) (wf : P.WF) (denote_eq : P.denote = Sigs.canon N I Φ fs)
    (safety_eq : P.safety = Sigs.canonSafety N I Φ ss) {f : String} {s : Sig} (v : FVar Φ f s) (hv : s.void = true)
    (xs : s.params.denS N) (this : JSValue) (vs : List JSValue)
    (args : ArgsRepS N I s.params (this :: vs) xs) (safe : FVar.safeS N v ss xs = true) :
    ∃ w t, Converges (fun n => runMethod ast n f this vs) (.ok (w, t)) ∧
      Ty.RepS N I s.result t (FVar.getS N v fs xs) := by
  rw [ArgsRepS_eq] at args
  have h := source_state_of erased wf denote_eq safety_eq v hv _ this vs args (by rw [← FVar.safeS_eq I]; exact safe)
  obtain ⟨w, t, hc, hr⟩ := h
  exact ⟨w, t, hc, by rw [Ty.repS_eq, FVar.conv_getS]; exact hr⟩

/-- `frame_of_fn` for a file whose readable definitions use named types. -/
theorem frame_of_fnS {fs0 : Fields} {g : String} {φ : Ty} (j : FIdx fs0 g φ) {Φ : Sigs} {P : TProgram Φ}
    {fns : Φ.denS N} (denote_eq : P.denote = Sigs.canon N I Φ fns) {bs : List Bool} (frames_eq : P.frames g = bs)
    {m name : String} {ps : Ctx} {t : Bool} (fn : FVar Φ m ⟨name, ("this", .record fs0) :: ps, .record fs0, t, true, true⟩)
    (hf : fn.flag bs = true) {f : Ctx.denS N (("this", .record fs0) :: ps) → Ty.den N (.record fs0)}
    (hfn : FVar.getS N fn fns = f) {acc : Ty.den N (.record fs0) → φ.den N} (hacc : ∀ r, recGet N I j r = acc r)
    (this : Ty.den N (.record fs0)) (args : ps.denS N) : acc (f (this, args)) = acc this := by
  rw [← hacc, ← hacc, ← hfn]
  apply Ty.conv_injective I φ
  rw [recGet_conv, recGet_conv]
  have h := frame_of j denote_eq frames_eq fn hf (Ty.conv N I (.record fs0) this) (Ctx.conv N I ps args)
  rw [show (Ty.conv N I (.record fs0) this, Ctx.conv N I ps args) = Ctx.conv N I (("this", .record fs0) :: ps) (this, args)
    from rfl, ← FVar.conv_getS] at h
  exact h

end

end Ariadne

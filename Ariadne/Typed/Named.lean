import Ariadne.Typed.Idiom

/-!
# Named types: structures and inductives

The denotation gives a record type nested pairs and a union nested sums, the same for every program, so
that the general theorem is proven once. A program's readable definitions use its own Lean types instead:
a `structure` for each named record type and an `inductive` for each named union.

`Names` lists a program's Lean types, keyed by the record's fields or the union's variants; `Ty.den N` is
`Ty.denote` with those types in place of the pairs and sums. `Isos N` says how each named type corresponds
to its fields (`view`, `make`) or its variants (`uelim`, `umake`), with the laws of an isomorphism; a
generated file gives them, and the kernel checks the laws. `TStmts.denoteRS` is `TStmts.denoteR` over these
types; a generated file checks its readable definitions against it by `rfl`. `Ty.conv` converts a value
to the denotation's, and `Ariadne.Proof.Named` proves, once, that the two denotations agree through it.
-/

namespace Ariadne

/-! ## Equality of types, by computation -/

mutual
  def Ty.eqb : Ty → Ty → Bool
    | .bool, .bool | .int, .int | .number, .number | .string, .string => true
    | .tag t, .tag t' => decide (t = t')
    | .lits a as, .lits b bs => decide (a = b) && decide (as = bs)
    | .option n τ, .option n' τ' => decide (n = n') && τ.eqb τ'
    | .record fs, .record fs' => fs.eqb fs'
    | .union k vs, .union k' vs' => decide (k = k') && vs.eqb vs'
    | .array τ, .array τ' => τ.eqb τ'
    | .map τ, .map τ' => τ.eqb τ'
    | _, _ => false

  def Fields.eqb : Fields → Fields → Bool
    | .nil, .nil => true
    | .cons f τ rest, .cons f' τ' rest' => decide (f = f') && τ.eqb τ' && rest.eqb rest'
    | _, _ => false

  def Variants.eqb : Variants → Variants → Bool
    | .one t fs, .one t' fs' => decide (t = t') && fs.eqb fs'
    | .cons t fs rest, .cons t' fs' rest' => decide (t = t') && fs.eqb fs' && rest.eqb rest'
    | _, _ => false
end

/-! ## Names -/

/-- A program's Lean types: for record types (by their fields) and unions (by their variants). -/
structure Names where
  recs : List (Fields × Type)
  unions : List (Variants × Type)

def Names.idx (N : Names) (fs : Fields) : Option (Fin N.recs.length) := N.recs.findFinIdx? (·.1.eqb fs)

def Names.uidx (N : Names) (vs : Variants) : Option (Fin N.unions.length) := N.unions.findFinIdx? (·.1.eqb vs)

mutual
  /-- `Ty.denote`, with the program's types for named records and unions. -/
  @[reducible] def Ty.den (N : Names) : Ty → Type
    | .bool => Bool
    | .int => Int
    | .number => Int
    | .string => JSString
    | .tag _ => Unit
    | .lits _ rest => Fin (rest.length + 1)
    | .option _ τ => Option (τ.den N)
    | .record fs => match N.idx fs with
      | some i => N.recs[i].2
      | none => fs.den N
    | .union _ vs => match N.uidx vs with
      | some i => N.unions[i].2
      | none => vs.den N
    | .array τ => List (τ.den N)
    | .map τ => List (JSString × τ.den N)

  @[reducible] def Fields.den (N : Names) : Fields → Type
    | .nil => Unit
    | .cons _ τ rest => τ.den N × rest.den N

  @[reducible] def Variants.den (N : Names) : Variants → Type
    | .one _ fs => fs.den N
    | .cons _ fs rest => fs.den N ⊕ rest.den N
end

/-! ## Variants -/

def VIdx.injS (N : Names) : VIdx vs t fs → fs.den N → vs.den N
  | .one, x => x
  | .head, x => .inl x
  | .there i, x => .inr (VIdx.injS N i x)

def VIdx.projS (N : Names) : VIdx vs t fs → vs.den N → Option (fs.den N)
  | .one, y => some y
  | .head, .inl y => some y
  | .head, .inr _ => none
  | .there _, .inl _ => none
  | .there i, .inr w => VIdx.projS N i w

def Variants.elimS (N : Names) {R : Type} : (vs : Variants) → vs.den N → (∀ {t fs}, VIdx vs t fs → fs.den N → R) → R
  | .one _ _, y, h => h .one y
  | .cons _ _ rest, u, h => match u with
    | .inl y => h .head y
    | .inr w => Variants.elimS N rest w fun i y => h (.there i) y

/-! ## Isomorphisms -/

/-- How each named type corresponds to its fields or variants. -/
structure Isos (N : Names) where
  view : (i : Fin N.recs.length) → N.recs[i].2 → Fields.den N N.recs[i].1
  make : (i : Fin N.recs.length) → Fields.den N N.recs[i].1 → N.recs[i].2
  view_make : ∀ i x, view i (make i x) = x
  make_view : ∀ i r, make i (view i r) = r
  /-- Case analysis of a union value: the handler gets the variant and its fields. -/
  uelim : (i : Fin N.unions.length) → {R : Type} → N.unions[i].2 →
    (∀ {t fs}, VIdx N.unions[i].1 t fs → Fields.den N fs → R) → R
  umake : (i : Fin N.unions.length) → Variants.den N N.unions[i].1 → N.unions[i].2
  uelim_umake : ∀ i {R : Type} x (h : ∀ {t fs}, VIdx N.unions[i].1 t fs → Fields.den N fs → R),
    uelim i (umake i x) h = Variants.elimS N _ x h
  umake_uelim : ∀ i u, umake i (uelim i u fun j y => VIdx.injS N j y) = u

mutual
  theorem Ty.eqb_eq_true : ∀ (a b : Ty), a.eqb b = true → a = b
    | .bool, b, h | .int, b, h | .number, b, h | .string, b, h => by cases b <;> simp_all [Ty.eqb]
    | .tag t, b, h => by cases b <;> simp_all [Ty.eqb]
    | .lits a as, b, h => by cases b <;> simp_all [Ty.eqb]
    | .option n τ, b, h => by
      cases b <;> simp only [Ty.eqb, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Ty.option.injEq] at h ⊢
      exact ⟨h.1, Ty.eqb_eq_true _ _ h.2⟩
    | .record fs, b, h => by
      cases b <;> simp only [Ty.eqb, reduceCtorEq, Ty.record.injEq] at h ⊢
      exact Fields.eqb_eq_true _ _ h
    | .union k vs, b, h => by
      cases b <;> simp only [Ty.eqb, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Ty.union.injEq] at h ⊢
      exact ⟨h.1, Variants.eqb_eq_true _ _ h.2⟩
    | .array τ, b, h => by
      cases b <;> simp only [Ty.eqb, reduceCtorEq, Ty.array.injEq] at h ⊢
      exact Ty.eqb_eq_true _ _ h
    | .map τ, b, h => by
      cases b <;> simp only [Ty.eqb, reduceCtorEq, Ty.map.injEq] at h ⊢
      exact Ty.eqb_eq_true _ _ h

  theorem Fields.eqb_eq_true : ∀ (a b : Fields), a.eqb b = true → a = b
    | .nil, b, h => by cases b <;> simp_all [Fields.eqb]
    | .cons f τ rest, b, h => by
      cases b <;> simp only [Fields.eqb, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Fields.cons.injEq] at h ⊢
      exact ⟨h.1.1, Ty.eqb_eq_true _ _ h.1.2, Fields.eqb_eq_true _ _ h.2⟩

  theorem Variants.eqb_eq_true : ∀ (a b : Variants), a.eqb b = true → a = b
    | .one t fs, b, h => by
      cases b <;> simp only [Variants.eqb, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Variants.one.injEq] at h ⊢
      exact ⟨h.1, Fields.eqb_eq_true _ _ h.2⟩
    | .cons t fs rest, b, h => by
      cases b <;> simp only [Variants.eqb, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Variants.cons.injEq] at h ⊢
      exact ⟨h.1.1, Fields.eqb_eq_true _ _ h.1.2, Variants.eqb_eq_true _ _ h.2⟩
end

theorem Names.idx_spec (N : Names) {fs : Fields} {i : Fin N.recs.length} (h : N.idx fs = some i) :
    N.recs[i].1 = fs :=
  Fields.eqb_eq_true _ _ (List.findFinIdx?_eq_some_iff.mp h).1

theorem Names.uidx_spec (N : Names) {vs : Variants} {i : Fin N.unions.length} (h : N.uidx vs = some i) :
    N.unions[i].1 = vs :=
  Variants.eqb_eq_true _ _ (List.findFinIdx?_eq_some_iff.mp h).1

/-! ## Named records and unions, generically -/

section
variable (N : Names) (I : Isos N)

/-- The type of a record with fields `fs`, given its name's index (`Names.idx`). -/
@[reducible] def recTy (fs : Fields) (o : Option (Fin N.recs.length)) : Type :=
  match o with
  | some i => N.recs[i].2
  | none => fs.den N

@[reducible] def unionTy (vs : Variants) (o : Option (Fin N.unions.length)) : Type :=
  match o with
  | some i => N.unions[i].2
  | none => vs.den N

def recViewAux (fs : Fields) : (o : Option (Fin N.recs.length)) → (∀ i, o = some i → N.recs[i].1 = fs) →
    recTy N fs o → fs.den N
  | some i, h, r => cast (congrArg (Fields.den N) (h i rfl)) (I.view i r)
  | none, _, r => r

def recMkAux (fs : Fields) : (o : Option (Fin N.recs.length)) → (∀ i, o = some i → N.recs[i].1 = fs) →
    fs.den N → recTy N fs o
  | some i, h, x => I.make i (cast (congrArg (Fields.den N) (h i rfl).symm) x)
  | none, _, x => x

def unionElimAux (vs : Variants) {R : Type} : (o : Option (Fin N.unions.length)) →
    (∀ i, o = some i → N.unions[i].1 = vs) → unionTy N vs o → (∀ {t fs}, VIdx vs t fs → fs.den N → R) → R
  | some i, h, u, k => I.uelim i u (fun {t fs} j y => k (cast (by rw [h i rfl]) j) y)
  | none, _, u, k => Variants.elimS N vs u k

def unionMkAux (vs : Variants) : (o : Option (Fin N.unions.length)) → (∀ i, o = some i → N.unions[i].1 = vs) →
    vs.den N → unionTy N vs o
  | some i, h, x => I.umake i (cast (congrArg (Variants.den N) (h i rfl).symm) x)
  | none, _, x => x

/-- A record's fields. -/
def recView (fs : Fields) (r : recTy N fs (N.idx fs)) : fs.den N :=
  recViewAux N I fs (N.idx fs) (fun _ h => N.idx_spec h) r

/-- The record with these fields. -/
def recMk (fs : Fields) (x : fs.den N) : recTy N fs (N.idx fs) :=
  recMkAux N I fs (N.idx fs) (fun _ h => N.idx_spec h) x

/-- Case analysis of a union value. -/
def unionElim (vs : Variants) {R : Type} (u : unionTy N vs (N.uidx vs)) (k : ∀ {t fs}, VIdx vs t fs → fs.den N → R) : R :=
  unionElimAux N I vs (N.uidx vs) (fun _ h => N.uidx_spec h) u k

/-- The union value of a variant. -/
def unionMk (vs : Variants) (x : vs.den N) : unionTy N vs (N.uidx vs) :=
  unionMkAux N I vs (N.uidx vs) (fun _ h => N.uidx_spec h) x

/-- A union value as its variant (`Variants.den`). -/
def unionView (vs : Variants) (u : unionTy N vs (N.uidx vs)) : vs.den N :=
  unionElim N I vs u fun j y => VIdx.injS N j y

end

/-! ## Values -/

def FIdx.getS (N : Names) : {fs : Fields} → FIdx fs f τ → fs.den N → τ.den N
  | .cons .., .here, (x, _) => x
  | .cons .., .there i, (_, xs) => FIdx.getS N i xs

def FIdx.setS (N : Names) : {fs : Fields} → FIdx fs f τ → fs.den N → τ.den N → fs.den N
  | .cons .., .here, (_, xs), y => (y, xs)
  | .cons .., .there i, (x, xs), y => (x, FIdx.setS N i xs y)

def Sel.pickS (N : Names) : Sel src fs → src.den N → fs.den N
  | .nil, _ => ()
  | .cons i rest, xs => (FIdx.getS N i xs, Sel.pickS N rest xs)
  | .absent _ rest, xs => (none, Sel.pickS N rest xs)

def Upd.applyS (N : Names) : {fs : Fields} → Upd src fs → src.den N → fs.den N → fs.den N
  | .nil, .nil, _, _ => ()
  | .cons .., .set i rest, xs, (_, r) => (FIdx.getS N i xs, Upd.applyS N rest xs r)
  | .cons .., .keep _ rest, xs, (a, r) => (a, Upd.applyS N rest xs r)

/-- `===` on primitives. -/
def Ty.beqS (N : Names) : (τ : Ty) → τ.den N → τ.den N → Bool
  | .bool, a, b => a == b
  | .int, a, b => a == b
  | .number, a, b => a == b
  | .string, a, b => a == b
  | .tag _, _, _ => true
  | .lits _ _, i, j => i == j
  | _, _, _ => false

mutual
  def Ty.defaultS (N : Names) (I : Isos N) : (τ : Ty) → τ.den N
    | .bool => false
    | .int => 0
    | .number => 0
    | .string => []
    | .tag _ => ()
    | .lits _ _ => 0
    | .option _ _ => none
    | .record fs => recMk N I fs (Fields.defaultS N I fs)
    | .union _ vs => unionMk N I vs (Variants.defaultS N I vs)
    | .array _ => []
    | .map _ => []

  def Fields.defaultS (N : Names) (I : Isos N) : (fs : Fields) → fs.den N
    | .nil => ()
    | .cons _ τ rest => (Ty.defaultS N I τ, Fields.defaultS N I rest)

  def Variants.defaultS (N : Names) (I : Isos N) : (vs : Variants) → vs.den N
    | .one _ fs => Fields.defaultS N I fs
    | .cons _ fs _ => .inl (Fields.defaultS N I fs)
end

def Narrowing.embedS (N : Names) (I : Isos N) : Narrowing σ τ → σ.den N → τ.den N
  | .some _ _, y => Option.some y
  | @Narrowing.variant vs t fs key i, z => unionMk N I vs (VIdx.injS N i (recView N I (.cons key (.tag t) fs) z).2)

def Op.applyS (N : Names) : Op σ τ → σ.den N → σ.den N → τ.den N
  | .add, a, b | .nadd, a, b => a + b
  | .sub, a, b | .nsub, a, b => a - b
  | .mul, a, b | .nmul, a, b => a * b
  | .concat, a, b => a ++ b
  | .eq _, a, b => Ty.beqS N _ a b
  | .ne _, a, b => !Ty.beqS N _ a b
  | .lt, a, b | .nlt, a, b => decide (a < b)
  | .le, a, b | .nle, a, b => decide (a ≤ b)
  | .gt, a, b | .ngt, a, b => decide (b < a)
  | .ge, a, b | .nge, a, b => decide (b ≤ a)
  | .slt, a, b => strLt a b
  | .sle, a, b => strLe a b
  | .sgt, a, b => strLt b a
  | .sge, a, b => strLe b a
  | .idiv, a, b => a.tdiv b
  | .imod, a, b | .nmod, a, b => a.tmod b
  | .ndiv, a, b => a.fdiv b

def Op.guardS (N : Names) : Op σ τ → Bool → σ.den N → σ.den N → Bool
  | .nadd, s, a, b => s && inRange (a + b)
  | .nsub, s, a, b => s && inRange (a - b)
  | .nmul, s, a, b => s && inRange (a * b)
  | .idiv, s, _, b | .imod, s, _, b => s && b != 0
  | .ndiv, s, a, b => s && (b != 0 && inRange a && inRange b)
  | .nmod, s, a, b => s && (b != 0 && inRange (a.tmod b))
  | _, s, _, _ => s

def SMethod.applyS (N : Names) : SMethod τ → JSString → JSString → τ.den N
  | .startsWith, s, t => strStartsWith s t
  | .endsWith, s, t => strEndsWith s t
  | .includes, s, t => strIncludes s t
  | .indexOf, s, t => strIndexOf s t

/-! ## Environments and functions -/

abbrev Ctx.denS (N : Names) : Ctx → Type
  | [] => Unit
  | (_, τ) :: Γ => τ.den N × Ctx.denS N Γ

def Var.getS (N : Names) : Var Γ x τ → Γ.denS N → τ.den N
  | .here, (v, _) => v
  | .there _ v, (_, ρ) => Var.getS N v ρ

def Var.setS (N : Names) : {Γ : Ctx} → Var Γ x τ → Γ.denS N → τ.den N → Γ.denS N
  | (_, _) :: _, .here, (_, ρ), y => (y, ρ)
  | (_, _) :: _, .there _ v, (a, ρ), y => (a, Var.setS N v ρ y)

def Var.narrowValS (N : Names) : {Γ : Ctx} → (v : Var Γ x τ) → Γ.denS N → σ.den N → (v.narrow σ).denS N
  | (_, _) :: _, .here, (_, ρ), y => show σ.den N × _ from (y, ρ)
  | (_, τ') :: _, .there _ v, (a, ρ), y => show τ'.den N × _ from (a, Var.narrowValS N v ρ y)

def Var.widenS (N : Names) : {Γ : Ctx} → (v : Var Γ x τ) → (σ.den N → τ.den N) → (v.narrow σ).denS N → Γ.denS N
  | (_, _) :: _, .here, e, ρ => let ρ' : σ.den N × _ := ρ; (e ρ'.1, ρ'.2)
  | (_, τ') :: _, .there _ v, e, ρ => let ρ' : τ'.den N × _ := ρ; (ρ'.1, Var.widenS N v e ρ'.2)

def Ctx.noneS (N : Names) (I : Isos N) : (ps : Ctx) → ps.denS N
  | [] => ()
  | (_, .option _ _) :: ps => (Option.none, Ctx.noneS N I ps)
  | (_, τ) :: ps => (Ty.defaultS N I τ, Ctx.noneS N I ps)

abbrev Sig.denS (N : Names) (s : Sig) : Type := s.params.denS N → s.result.den N

abbrev Sigs.denS (N : Names) : Sigs → Type
  | [] => Unit
  | s :: Φ => s.denS N × Sigs.denS N Φ

abbrev Sigs.safetyS (N : Names) : Sigs → Type
  | [] => Unit
  | s :: Φ => (s.params.denS N → Bool) × Sigs.safetyS N Φ

def FVar.getS (N : Names) : FVar Φ f s → Φ.denS N → s.denS N
  | .here, (g, _) => g
  | .there v, (_, fs) => FVar.getS N v fs

def FVar.safeS (N : Names) : FVar Φ f s → Φ.safetyS N → s.params.denS N → Bool
  | .here, (g, _) => g
  | .there v, (_, fs) => FVar.safeS N v fs

/-! ## Records through their fields -/

section
variable (N : Names) (I : Isos N)

/-- `r.f`. -/
def recGet {fs : Fields} (i : FIdx fs f τ) (r : Ty.den N (.record fs)) : τ.den N := FIdx.getS N i (recView N I fs r)

/-- A record literal. -/
def recSel {fs : Fields} (sel : Sel src fs) (es : src.den N) : Ty.den N (.record fs) := recMk N I fs (Sel.pickS N sel es)

/-- `{ ...r, entries }`. -/
def recUpd {fs : Fields} (u : Upd src fs) (es : src.den N) (r : Ty.den N (.record fs)) : Ty.den N (.record fs) :=
  recMk N I fs (Upd.applyS N u es (recView N I fs r))

/-- `this` with field `i` replaced. -/
def recSet {fs : Fields} (i : FIdx fs f τ) (r : Ty.den N (.record fs)) (y : τ.den N) : Ty.den N (.record fs) :=
  recMk N I fs (FIdx.setS N i (recView N I fs r) y)

/-! ## Expressions -/

mutual
  def TExpr.denS (fs : Φ.denS N) : TExpr Φ Γ τ → Γ.denS N → τ.den N
    | .bool b, _ => b
    | .int n, _ => n
    | .str s, _ => s
    | .tagLit _, _ => ()
    | .litIn _ _ i, _ => i
    | .undef .., _ => none
    | .null .., _ => none
    | .var v, ρ => Var.getS N v ρ
    | .widen M e, ρ => Narrowing.embedS N I M (e.denS fs ρ)
    | .not e, ρ => !e.denS fs ρ
    | .neg e, ρ => -e.denS fs ρ
    | .bin op a b, ρ => Op.applyS N op (a.denS fs ρ) (b.denS fs ρ)
    | .and a b, ρ => a.denS fs ρ && b.denS fs ρ
    | .or a b, ρ => a.denS fs ρ || b.denS fs ρ
    | .cond c a b, ρ => if c.denS fs ρ then a.denS fs ρ else b.denS fs ρ
    | .isNull _ e, ρ => (e.denS fs ρ).isNone
    | .notNull _ e, ρ => (e.denS fs ρ).isSome
    | .condNull v _ a b, ρ => match Var.getS N v ρ with
      | none => a.denS fs ρ
      | some y => b.denS fs (Var.narrowValS N v ρ y)
    | .condNotNull v _ a b, ρ => match Var.getS N v ρ with
      | some y => a.denS fs (Var.narrowValS N v ρ y)
      | none => b.denS fs ρ
    | .coalesce _ a b, ρ => match a.denS fs ρ with
      | some x => x
      | none => b.denS fs ρ
    | .call fn _ args, ρ => FVar.getS N fn fs (args.denS fs ρ)
    | .record es sel _, ρ => recSel N I sel (es.denS fs ρ)
    | .update r es u _, ρ => recUpd N I u (es.denS fs ρ) (r.denS fs ρ)
    | .field e i _, ρ => recGet N I i (e.denS fs ρ)
    | .num n, _ => n
    | .negNum n _, _ => -n
    | .nneg e, ρ => -e.denS fs ρ
    | .iinc up e, ρ | .ninc up e, ρ => bif up then e.denS fs ρ + 1 else e.denS fs ρ - 1
    | .array es, ρ => es.denS fs ρ
    | .length a, ρ => ((a.denS fs ρ).length : Int)
    | .slength s, ρ => ((s.denS fs ρ).length : Int)
    | .smethod m s t, ρ => SMethod.applyS N m (s.denS fs ρ) (t.denS fs ρ)
    | .slice1 s a, ρ => strSlice (s.denS fs ρ) (a.denS fs ρ) (s.denS fs ρ).length
    | .slice2 s a b, ρ => strSlice (s.denS fs ρ) (a.denS fs ρ) (b.denS fs ρ)
    | .index a i, ρ => listIndex (a.denS fs ρ) (i.denS fs ρ)
    | .includes _ a e, ρ => (a.denS fs ρ).any fun y => Ty.beqS N _ y (e.denS fs ρ)
    | .any a p, ρ => (a.denS fs ρ).any (p.denS fs ρ)
    | .all a p, ρ => (a.denS fs ρ).all (p.denS fs ρ)
    | .find a p, ρ => (a.denS fs ρ).find? (p.denS fs ρ)
    | .filter a p, ρ => (a.denS fs ρ).filter (p.denS fs ρ)
    | .map a f, ρ => (a.denS fs ρ).map (f.denS fs ρ)
    | .sorted a c, ρ => sortedBy (c.denS fs ρ) (a.denS fs ρ)
    | .newMap _, _ => []
    | .stateGet v i _ k, ρ => mapGet (recGet N I i (Var.getS N v ρ)) (k.denS fs ρ)
    | .stateHas v i k, ρ => (mapGet (recGet N I i (Var.getS N v ρ)) (k.denS fs ρ)).isSome
    | .stateSize v i, ρ => ((recGet N I i (Var.getS N v ρ)).length : Int)
    | .callThis fn v args, ρ => FVar.getS N fn fs (Var.getS N v ρ, args.denS fs ρ)

  def TArgs.denS (fs : Φ.denS N) : TArgs Φ Γ ps → Γ.denS N → ps.denS N
    | .nil, _ => ()
    | .cons e rest, ρ => (e.denS fs ρ, rest.denS fs ρ)
    | .omitted _, _ => Ctx.noneS N I _

  def TEntries.denS (fs : Φ.denS N) : TEntries Φ Γ src → Γ.denS N → src.den N
    | .nil, _ => ()
    | .cons _ e rest, ρ => (e.denS fs ρ, rest.denS fs ρ)

  def TFn.denS (fs : Φ.denS N) : TFn Φ Γ τ σ → Γ.denS N → τ.den N → σ.den N
    | .arrow _ body, ρ => fun y => body.denS fs (y, ρ)
    | .const body, ρ => fun _ => body.denS fs ρ
    | .ref fn _, _ => fun y => FVar.getS N fn fs (y, ())

  def TCmp.denS (fs : Φ.denS N) : TCmp Φ Γ τ → Γ.denS N → τ.den N → τ.den N → Int
    | .arrow _ _ body, ρ => fun y z => body.denS fs (y, z, ρ)
    | .ref fn _, _ => fun y z => FVar.getS N fn fs (y, z, ())

  def TElems.denS (fs : Φ.denS N) : TElems Φ Γ τ → Γ.denS N → List (τ.den N)
    | .nil, _ => []
    | .cons e rest, ρ => e.denS fs ρ :: rest.denS fs ρ
    | .spread a rest, ρ => a.denS fs ρ ++ rest.denS fs ρ
    | .spreadKeys v i rest, ρ => (recGet N I i (Var.getS N v ρ)).map Prod.fst ++ rest.denS fs ρ
    | .spreadValues v i rest, ρ => (recGet N I i (Var.getS N v ρ)).map Prod.snd ++ rest.denS fs ρ
end

mutual
  def TExpr.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TExpr Φ Γ τ → Γ.denS N → Bool
    | .bool _, _ | .int _, _ | .str _, _ | .tagLit _, _ | .litIn .., _ | .undef .., _ | .null .., _ | .var _, _
    | .num _, _ | .negNum .., _ => true
    | .widen _ e, ρ | .not e, ρ | .neg e, ρ | .isNull _ e, ρ | .notNull _ e, ρ | .field e _ _, ρ | .iinc _ e, ρ
    | .length e, ρ | .slength e, ρ => e.safeS fs ss ρ
    | .index a b, ρ | .includes _ a b, ρ | .smethod _ a b, ρ | .slice1 a b, ρ =>
      andT a.trivial (a.safeS fs ss ρ) b.trivial (b.safeS fs ss ρ)
    | .slice2 s a b, ρ => andT s.trivial (s.safeS fs ss ρ) (a.trivial && b.trivial)
      (andT a.trivial (a.safeS fs ss ρ) b.trivial (b.safeS fs ss ρ))
    | .bin op a b, ρ => Op.guardS N op (andT a.trivial (a.safeS fs ss ρ) b.trivial (b.safeS fs ss ρ))
      (TExpr.denS N I fs a ρ) (TExpr.denS N I fs b ρ)
    | .nneg e, ρ => (e.trivial || e.safeS fs ss ρ) && inRange (-TExpr.denS N I fs e ρ)
    | .ninc up e, ρ => (e.trivial || e.safeS fs ss ρ) &&
      inRange (bif up then TExpr.denS N I fs e ρ + 1 else TExpr.denS N I fs e ρ - 1)
    | .and a b, ρ => andT a.trivial (a.safeS fs ss ρ) b.trivial
      (if TExpr.denS N I fs a ρ then b.safeS fs ss ρ else true)
    | .or a b, ρ => andT a.trivial (a.safeS fs ss ρ) b.trivial
      (if TExpr.denS N I fs a ρ then true else b.safeS fs ss ρ)
    | .cond c a b, ρ => andT c.trivial (c.safeS fs ss ρ) (a.trivial && b.trivial)
      (if TExpr.denS N I fs c ρ then a.trivial || a.safeS fs ss ρ else b.trivial || b.safeS fs ss ρ)
    | .condNull v _ a b, ρ => match Var.getS N v ρ with
      | none => a.trivial || a.safeS fs ss ρ
      | some y => b.trivial || b.safeS fs ss (Var.narrowValS N v ρ y)
    | .condNotNull v _ a b, ρ => match Var.getS N v ρ with
      | some y => a.trivial || a.safeS fs ss (Var.narrowValS N v ρ y)
      | none => b.trivial || b.safeS fs ss ρ
    | .coalesce _ a b, ρ => andT a.trivial (a.safeS fs ss ρ) b.trivial (match TExpr.denS N I fs a ρ with
      | some _ => true
      | none => b.safeS fs ss ρ)
    | @TExpr.call _ _ _ s fn _ args, ρ =>
      andT args.trivial (args.safeS fs ss ρ) s.trivial (FVar.safeS N fn ss (TArgs.denS N I fs args ρ))
    | .record es _ _, ρ | .array es, ρ => es.safeS fs ss ρ
    | .update r es _ _, ρ => andT r.trivial (r.safeS fs ss ρ) es.trivial (es.safeS fs ss ρ)
    | .any a p, ρ | .find a p, ρ => andT a.trivial (a.safeS fs ss ρ) p.trivial
      (anySafe (TFn.denS N I fs p ρ) (p.safeS fs ss ρ) (TExpr.denS N I fs a ρ))
    | .all a p, ρ => andT a.trivial (a.safeS fs ss ρ) p.trivial
      (allSafe (TFn.denS N I fs p ρ) (p.safeS fs ss ρ) (TExpr.denS N I fs a ρ))
    | .filter a p, ρ | .map a p, ρ => andT a.trivial (a.safeS fs ss ρ) p.trivial
      ((TExpr.denS N I fs a ρ).all (p.safeS fs ss ρ))
    | .sorted a c, ρ => (a.trivial || a.safeS fs ss ρ) &&
      sortSafe (TCmp.denS N I fs c ρ) c.trivial (c.safeS fs ss ρ) (TExpr.denS N I fs a ρ)
    | .newMap _, _ | .stateSize _ _, _ => true
    | .stateGet _ _ _ k, ρ | .stateHas _ _ k, ρ => k.safeS fs ss ρ
    | .callThis (t := t) fn v args, ρ =>
      andT args.trivial (args.safeS fs ss ρ) t (FVar.safeS N fn ss (Var.getS N v ρ, TArgs.denS N I fs args ρ))

  def TArgs.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TArgs Φ Γ ps → Γ.denS N → Bool
    | .nil, _ | .omitted _, _ => true
    | .cons e rest, ρ => andT e.trivial (e.safeS fs ss ρ) rest.trivial (rest.safeS fs ss ρ)

  def TEntries.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TEntries Φ Γ src → Γ.denS N → Bool
    | .nil, _ => true
    | .cons _ e rest, ρ => andT e.trivial (e.safeS fs ss ρ) rest.trivial (rest.safeS fs ss ρ)

  def TFn.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TFn Φ Γ τ σ → Γ.denS N → τ.den N → Bool
    | .arrow _ body, ρ => fun y => body.safeS fs ss (y, ρ)
    | .const body, ρ => fun _ => body.safeS fs ss ρ
    | .ref fn _, _ => fun y => FVar.safeS N fn ss (y, ())

  def TCmp.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TCmp Φ Γ τ → Γ.denS N → τ.den N → τ.den N → Bool
    | .arrow _ _ body, ρ => fun y z => body.safeS fs ss (y, z, ρ)
    | .ref fn _, _ => fun y z => FVar.safeS N fn ss (y, z, ())

  def TElems.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TElems Φ Γ τ → Γ.denS N → Bool
    | .nil, _ => true
    | .cons e rest, ρ | .spread e rest, ρ => andT e.trivial (e.safeS fs ss ρ) rest.trivial (rest.safeS fs ss ρ)
    | .spreadKeys _ _ rest, ρ | .spreadValues _ _ rest, ρ => rest.safeS fs ss ρ
end

end

/-! ## Statements -/

/-- What follows a statement list, on environments of named types. -/
structure KS (N : Names) (Γ : Ctx) (R : Type) where
  normal : Γ.denS N → R
  brk : Γ.denS N → R
  cont : Γ.denS N → R

def KS.map {N : Names} (f : Γ'.denS N → Γ.denS N) (k : KS N Γ R) : KS N Γ' R := ⟨k.normal ∘ f, k.brk ∘ f, k.cont ∘ f⟩

def KS.all {N : Names} (r : Γ.denS N → R) : KS N Γ R := ⟨r, r, r⟩

@[reducible] def Ctx.tupS (N : Names) : Ctx → Type
  | [] => Unit
  | [(_, τ)] => τ.den N
  | (_, τ) :: p :: Γ => τ.den N × Ctx.tupS N (p :: Γ)

def Ctx.tconsS (N : Names) : {x : String} → {τ : Ty} → {Δ : Ctx} → τ.den N → Δ.tupS N → Ctx.tupS N ((x, τ) :: Δ)
  | _, _, [], a, _ => a
  | _, _, _ :: _, a, t => (a, t)

def Ctx.theadS (N : Names) : {x : String} → {τ : Ty} → {Δ : Ctx} → Ctx.tupS N ((x, τ) :: Δ) → τ.den N
  | _, _, [], a => a
  | _, _, _ :: _, (a, _) => a

def Ctx.ttailS (N : Names) : {x : String} → {τ : Ty} → {Δ : Ctx} → Ctx.tupS N ((x, τ) :: Δ) → Δ.tupS N
  | _, _, [], _ => ()
  | _, _, _ :: _, (_, t) => t

def Ctx.projS (N : Names) : (Γ : Ctx) → (m : Mask) → Γ.denS N → (Γ.sub m).tupS N
  | [], _, _ => ()
  | _ :: _, [], _ => ()
  | (_, _) :: Γ, true :: m, (a, ρ) => Ctx.tconsS N a (Ctx.projS N Γ m ρ)
  | (_, _) :: Γ, false :: m, (_, ρ) => Ctx.projS N Γ m ρ

def Ctx.mergeS (N : Names) : (Γ : Ctx) → (m : Mask) → Γ.denS N → (Γ.sub m).tupS N → Γ.denS N
  | [], _, ρ, _ => ρ
  | _ :: _, [], ρ, _ => ρ
  | (_, _) :: Γ, true :: m, (_, ρ), s => (Ctx.theadS N s, Ctx.mergeS N Γ m ρ (Ctx.ttailS N s))
  | (_, _) :: Γ, false :: m, (a, ρ), s => (a, Ctx.mergeS N Γ m ρ s)

section
variable (N : Names) (I : Isos N)

/-- The narrowed variable's value in a `switch` case: the variant record. -/
def vrecOf (key : String) {vs : Variants} {t : TagLit} {fs : Fields} (_ : VIdx vs t fs) (y : fs.den N) :
    Ty.den N (vrec key t fs) :=
  recMk N I (.cons key (.tag t) fs) ((), y)

mutual
  /-- `TStmts.denoteR` over the program's named types. -/
  def TStmts.denoteRS (fs : Φ.denS N) {R : Type} (r : τ.den N → R) : TStmts Φ Γ τ → KS N Γ R → Γ.denS N → R
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => rest.denoteRS fs r (k.map Prod.snd) (TExpr.denS N I fs e ρ, ρ)
    | .ret e _, _, ρ => r (TExpr.denS N I fs e ρ)
    | .ite c yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteRS fs r k (Ctx.mergeS N Γ (Mask.or yes.writes no.writes) ρ
          (if TExpr.denS N I fs c ρ then
            yes.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))) ρ
          else
            no.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))) ρ))
      else if TExpr.denS N I fs c ρ then yes.denoteRS fs r { k with normal := rest.denoteRS fs r k } ρ
      else no.denoteRS fs r { k with normal := rest.denoteRS fs r k } ρ
    | .block body rest, k, ρ => body.denoteRS fs r { k with normal := rest.denoteRS fs r k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => rest.denoteRS fs r (k.map Prod.snd) (TExpr.denS N I fs e ρ, ρ)
    | .assign v e rest, k, ρ => rest.denoteRS fs r k (Var.setS N v ρ (TExpr.denS N I fs e ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail ρ ((TExpr.denS N I fs a ρ).foldl
          (fun s y => body.denoteRS fs (fun _ => s) (KS.map Prod.snd (KS.all (Ctx.projS N Γ body.writes.tail)))
            (y, Ctx.mergeS N Γ body.writes.tail ρ s))
          (Ctx.projS N Γ body.writes.tail ρ)))
      else
        forIn (TExpr.denS N I fs a ρ) (fun y next exit s =>
            body.denoteRS fs r (KS.map Prod.snd ⟨next ∘ Ctx.projS N Γ body.writes.tail,
              exit ∘ Ctx.projS N Γ body.writes.tail, next ∘ Ctx.projS N Γ body.writes.tail⟩)
              (y, Ctx.mergeS N Γ body.writes.tail ρ s))
          (fun s => rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail ρ s)) (Ctx.projS N Γ body.writes.tail ρ)
    | .forEntries _ _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail.tail ρ ((TExpr.denS N I fs a ρ).zipIdx.foldl
          (fun s p => body.denoteRS fs (fun _ => s)
            (KS.map Prod.snd (KS.map Prod.snd (KS.all (Ctx.projS N Γ body.writes.tail.tail))))
            (p.1, (p.2 : Int), Ctx.mergeS N Γ body.writes.tail.tail ρ s))
          (Ctx.projS N Γ body.writes.tail.tail ρ)))
      else
        forIn (TExpr.denS N I fs a ρ).zipIdx (fun p next exit s =>
            body.denoteRS fs r (KS.map Prod.snd (KS.map Prod.snd ⟨next ∘ Ctx.projS N Γ body.writes.tail.tail,
              exit ∘ Ctx.projS N Γ body.writes.tail.tail, next ∘ Ctx.projS N Γ body.writes.tail.tail⟩))
              (p.1, (p.2 : Int), Ctx.mergeS N Γ body.writes.tail.tail ρ s))
          (fun s => rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail.tail ρ s))
          (Ctx.projS N Γ body.writes.tail.tail ρ)
    | .ifNull v _ yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteRS fs r k (Ctx.mergeS N Γ (Mask.or yes.writes no.writes) ρ (match Var.getS N v ρ with
          | none => yes.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))) ρ
          | some y => no.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.map (Var.widenS N v some) (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))))
              (Var.narrowValS N v ρ y)))
      else match Var.getS N v ρ with
        | none => yes.denoteRS fs r { k with normal := rest.denoteRS fs r k } ρ
        | some y => no.denoteRS fs r (KS.map (Var.widenS N v some) { k with normal := rest.denoteRS fs r k })
            (Var.narrowValS N v ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match Var.getS N v ρ with
      | none => yes.denoteRS fs r k ρ
      | some y => rest.denoteRS fs r (k.map (Var.widenS N v some)) (Var.narrowValS N v ρ y)
    | .ifNotNull v _ yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteRS fs r k (Ctx.mergeS N Γ (Mask.or yes.writes no.writes) ρ (match Var.getS N v ρ with
          | some y => yes.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.map (Var.widenS N v some) (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))))
              (Var.narrowValS N v ρ y)
          | none => no.denoteRS fs (fun _ => Ctx.projS N Γ (Mask.or yes.writes no.writes) ρ)
              (KS.all (Ctx.projS N Γ (Mask.or yes.writes no.writes))) ρ))
      else match Var.getS N v ρ with
        | some y => yes.denoteRS fs r (KS.map (Var.widenS N v some) { k with normal := rest.denoteRS fs r k })
            (Var.narrowValS N v ρ y)
        | none => no.denoteRS fs r { k with normal := rest.denoteRS fs r k } ρ
    | .switchG v _ arms rest, k, ρ =>
      if arms.closed then
        rest.denoteRS fs r k (Ctx.mergeS N Γ arms.writes ρ (unionElim N I _ (Var.getS N v ρ) fun i y =>
          arms.denoteRS fs (fun _ => Ctx.projS N Γ arms.writes ρ) (KS.all (Ctx.projS N Γ arms.writes)) ρ i y
            (Ctx.projS N Γ arms.writes ρ)))
      else
        unionElim N I _ (Var.getS N v ρ) fun i y =>
          arms.denoteRS fs r { k with normal := rest.denoteRS fs r k, brk := rest.denoteRS fs r k } ρ i y
            (rest.denoteRS fs r k ρ)
    | .forRange _ v body rest, k, ρ =>
      if body.direct then
        rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail ρ ((range (Var.getS N v ρ)).foldl
          (fun s j => body.denoteRS fs (fun _ => s) (KS.map Prod.snd (KS.all (Ctx.projS N Γ body.writes.tail)))
            (j, Ctx.mergeS N Γ body.writes.tail ρ s))
          (Ctx.projS N Γ body.writes.tail ρ)))
      else
        forIn (range (Var.getS N v ρ)) (fun j next exit s =>
            body.denoteRS fs r (KS.map Prod.snd ⟨next ∘ Ctx.projS N Γ body.writes.tail,
              exit ∘ Ctx.projS N Γ body.writes.tail, next ∘ Ctx.projS N Γ body.writes.tail⟩)
              (j, Ctx.mergeS N Γ body.writes.tail ρ s))
          (fun s => rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes.tail ρ s)) (Ctx.projS N Γ body.writes.tail ρ)
    | .whileLoop c body rest, k, ρ =>
      whileDo (fun s => TExpr.denS N I fs c (Ctx.mergeS N Γ body.writes ρ s))
        (fun next exit s => body.denoteRS fs r ⟨next ∘ Ctx.projS N Γ body.writes, exit ∘ Ctx.projS N Γ body.writes,
          next ∘ Ctx.projS N Γ body.writes⟩ (Ctx.mergeS N Γ body.writes ρ s))
        (fun s => rest.denoteRS fs r k (Ctx.mergeS N Γ body.writes ρ s)) (Ctx.projS N Γ body.writes ρ)
    | .stateSet v i _ key e rest, k, ρ =>
      rest.denoteRS fs r k (Var.setS N v ρ (recSet N I i (Var.getS N v ρ)
        (mapPut (recGet N I i (Var.getS N v ρ)) (TExpr.denS N I fs key ρ) (TExpr.denS N I fs e ρ))))
    | .stateDelete v i _ key rest, k, ρ =>
      rest.denoteRS fs r k (Var.setS N v ρ (recSet N I i (Var.getS N v ρ)
        (mapDel (recGet N I i (Var.getS N v ρ)) (TExpr.denS N I fs key ρ))))
    | .callVoid fn v args rest, k, ρ =>
      rest.denoteRS fs r k (Var.setS N v ρ (FVar.getS N fn fs (Var.getS N v ρ, TArgs.denS N I fs args ρ)))
    | .retVoid v _, _, ρ => r (Var.getS N v ρ)

  def TArms.firstRS {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (fs : Φ.denS N) {R : Type} (r : τ.den N → R) : TArms Φ Γ τ v → KS N Γ R → Γ.denS N → R
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstRS fs r k ρ
    | .wide _ body _, k, ρ => body.denoteRS fs r k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.denoteRS {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      {t : TagLit} {fds : Fields} (fs : Φ.denS N) {R : Type} (r : τ.den N → R) :
      TArms Φ Γ τ v → KS N Γ R → Γ.denS N → VIdx vs0 t fds → fds.den N → R → R
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstRS fs r k ρ
      else rest.denoteRS fs r k ρ i y (if l = none then rest.firstRS fs r k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.denoteRS fs r k ρ
      else rest.denoteRS fs r k ρ i y (if l = none then body.denoteRS fs r k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match VIdx.projS N i' (VIdx.injS N i y) with
      | some y' => body.denoteRS fs r (k.map (Var.widenS N v (Narrowing.embedS N I (.variant i'))))
          (Var.narrowValS N v ρ (vrecOf N I key i' y'))
      | none => rest.denoteRS fs r k ρ i y d
end

mutual
  /-- `TStmts.safe` over the program's named types. -/
  def TStmts.safeS (fs : Φ.denS N) (ss : Φ.safetyS N) : TStmts Φ Γ τ → KS N Γ Bool → Γ.denS N → Bool
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => (e.trivial || TExpr.safeS N I fs ss e ρ) &&
      rest.safeS fs ss (k.map Prod.snd) (TExpr.denS N I fs e ρ, ρ)
    | .ret e _, _, ρ => e.trivial || TExpr.safeS N I fs ss e ρ
    | .ite c yes no rest, k, ρ => (c.trivial || TExpr.safeS N I fs ss c ρ) &&
      (if TExpr.denS N I fs c ρ then yes.safeS fs ss { k with normal := rest.safeS fs ss k } ρ
       else no.safeS fs ss { k with normal := rest.safeS fs ss k } ρ)
    | .block body rest, k, ρ => body.safeS fs ss { k with normal := rest.safeS fs ss k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => (e.trivial || TExpr.safeS N I fs ss e ρ) &&
      rest.safeS fs ss (k.map Prod.snd) (TExpr.denS N I fs e ρ, ρ)
    | .assign v e rest, k, ρ => (e.trivial || TExpr.safeS N I fs ss e ρ) &&
      rest.safeS fs ss k (Var.setS N v ρ (TExpr.denS N I fs e ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ => (a.trivial || TExpr.safeS N I fs ss a ρ) &&
      forIn (TExpr.denS N I fs a ρ) (fun y next exit ρ' => body.safeS fs ss (KS.map Prod.snd ⟨next, exit, next⟩) (y, ρ'))
        (rest.safeS fs ss k) ρ
    | .forEntries _ _ a body rest, k, ρ => (a.trivial || TExpr.safeS N I fs ss a ρ) &&
      forIn (TExpr.denS N I fs a ρ).zipIdx (fun p next exit ρ' =>
          body.safeS fs ss (KS.map Prod.snd (KS.map Prod.snd ⟨next, exit, next⟩)) (p.1, (p.2 : Int), ρ'))
        (rest.safeS fs ss k) ρ
    | .ifNull v _ yes no rest, k, ρ => match Var.getS N v ρ with
      | none => yes.safeS fs ss { k with normal := rest.safeS fs ss k } ρ
      | some y => no.safeS fs ss (KS.map (Var.widenS N v some) { k with normal := rest.safeS fs ss k })
          (Var.narrowValS N v ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match Var.getS N v ρ with
      | none => yes.safeS fs ss k ρ
      | some y => rest.safeS fs ss (k.map (Var.widenS N v some)) (Var.narrowValS N v ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match Var.getS N v ρ with
      | some y => yes.safeS fs ss (KS.map (Var.widenS N v some) { k with normal := rest.safeS fs ss k })
          (Var.narrowValS N v ρ y)
      | none => no.safeS fs ss { k with normal := rest.safeS fs ss k } ρ
    | .switchG v _ arms rest, k, ρ =>
      unionElim N I _ (Var.getS N v ρ) fun i y =>
        arms.safeS fs ss { k with normal := rest.safeS fs ss k, brk := rest.safeS fs ss k } ρ i y (rest.safeS fs ss k ρ)
    | .forRange _ v body rest, k, ρ =>
      forIn (range (Var.getS N v ρ)) (fun j next exit ρ' => body.safeS fs ss (KS.map Prod.snd ⟨next, exit, next⟩) (j, ρ'))
        (rest.safeS fs ss k) ρ
    | .whileLoop c body rest, k, ρ =>
      whileSafe (fun ρ' => TExpr.denS N I fs c ρ') (fun next exit ρ' => body.safeS fs ss ⟨next, exit, next⟩ ρ')
        (rest.safeS fs ss k) ρ
    | .stateSet v i _ key e rest, k, ρ => andT key.trivial (TExpr.safeS N I fs ss key ρ) e.trivial
        (TExpr.safeS N I fs ss e ρ) &&
      rest.safeS fs ss k (Var.setS N v ρ (recSet N I i (Var.getS N v ρ)
        (mapPut (recGet N I i (Var.getS N v ρ)) (TExpr.denS N I fs key ρ) (TExpr.denS N I fs e ρ))))
    | .stateDelete v i _ key rest, k, ρ => (key.trivial || TExpr.safeS N I fs ss key ρ) &&
      rest.safeS fs ss k (Var.setS N v ρ (recSet N I i (Var.getS N v ρ)
        (mapDel (recGet N I i (Var.getS N v ρ)) (TExpr.denS N I fs key ρ))))
    | .callVoid (t := t) fn v args rest, k, ρ =>
      andT args.trivial (TArgs.safeS N I fs ss args ρ) t (FVar.safeS N fn ss (Var.getS N v ρ, TArgs.denS N I fs args ρ)) &&
        rest.safeS fs ss k (Var.setS N v ρ (FVar.getS N fn fs (Var.getS N v ρ, TArgs.denS N I fs args ρ)))
    | .retVoid _ _, _, _ => true

  def TArms.firstSafeS {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (fs : Φ.denS N) (ss : Φ.safetyS N) : TArms Φ Γ τ v → KS N Γ Bool → Γ.denS N → Bool
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstSafeS fs ss k ρ
    | .wide _ body _, k, ρ => body.safeS fs ss k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.safeS {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      {t : TagLit} {fds : Fields} (fs : Φ.denS N) (ss : Φ.safetyS N) :
      TArms Φ Γ τ v → KS N Γ Bool → Γ.denS N → VIdx vs0 t fds → fds.den N → Bool → Bool
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstSafeS fs ss k ρ
      else rest.safeS fs ss k ρ i y (if l = none then rest.firstSafeS fs ss k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.safeS fs ss k ρ
      else rest.safeS fs ss k ρ i y (if l = none then body.safeS fs ss k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match VIdx.projS N i' (VIdx.injS N i y) with
      | some y' => body.safeS fs ss (k.map (Var.widenS N v (Narrowing.embedS N I (.variant i'))))
          (Var.narrowValS N v ρ (vrecOf N I key i' y'))
      | none => rest.safeS fs ss k ρ i y d
end

/-- A function body over the program's named types. -/
def TStmts.denoteRSFn (fs : Φ.denS N) (body : TStmts Φ Γ τ) : Γ.denS N → τ.den N :=
  body.denoteRS N I fs id (KS.all fun _ => Ty.defaultS N I τ)

def TStmts.safeFnS (fs : Φ.denS N) (ss : Φ.safetyS N) (body : TStmts Φ Γ τ) : Γ.denS N → Bool :=
  if body.trivial then fun _ => true else body.safeS N I fs ss (KS.all fun _ => true)

end

/-! ## Conversions to the denotation's values -/

section
variable (N : Names) (I : Isos N)

mutual
  /-- A value of the program's types as the denotation's. -/
  def Ty.conv : (τ : Ty) → τ.den N → τ.denote
    | .bool, x | .int, x | .number, x | .string, x | .tag _, x | .lits _ _, x => x
    | .option _ τ, x => x.map (Ty.conv τ)
    | .record fs, r => Fields.conv fs (recView N I fs r)
    | .union _ vs, u => Variants.conv vs (unionView N I vs u)
    | .array τ, xs => xs.map (Ty.conv τ)
    | .map τ, m => m.map fun p => (p.1, Ty.conv τ p.2)

  def Fields.conv : (fs : Fields) → fs.den N → fs.denote
    | .nil, _ => ()
    | .cons _ τ rest, (x, xs) => (Ty.conv τ x, Fields.conv rest xs)

  def Variants.conv : (vs : Variants) → vs.den N → vs.denote
    | .one _ fs, x => Fields.conv fs x
    | .cons _ fs _, .inl x => .inl (Fields.conv fs x)
    | .cons _ _ rest, .inr y => .inr (Variants.conv rest y)
end

mutual
  /-- A value of the denotation as the program's types'. -/
  def Ty.convInv : (τ : Ty) → τ.denote → τ.den N
    | .bool, x | .int, x | .number, x | .string, x | .tag _, x | .lits _ _, x => x
    | .option _ τ, x => x.map (Ty.convInv τ)
    | .record fs, r => recMk N I fs (Fields.convInv fs r)
    | .union _ vs, u => unionMk N I vs (Variants.convInv vs u)
    | .array τ, xs => xs.map (Ty.convInv τ)
    | .map τ, m => m.map fun p => (p.1, Ty.convInv τ p.2)

  def Fields.convInv : (fs : Fields) → fs.denote → fs.den N
    | .nil, _ => ()
    | .cons _ τ rest, (x, xs) => (Ty.convInv τ x, Fields.convInv rest xs)

  def Variants.convInv : (vs : Variants) → vs.denote → vs.den N
    | .one _ fs, x => Fields.convInv fs x
    | .cons _ fs _, .inl x => .inl (Fields.convInv fs x)
    | .cons _ _ rest, .inr y => .inr (Variants.convInv rest y)
end

def Ctx.conv : (Γ : Ctx) → Γ.denS N → Γ.denote
  | [], _ => ()
  | (_, τ) :: Γ, (x, ρ) => (Ty.conv N I τ x, Ctx.conv Γ ρ)

def Ctx.convInv : (Γ : Ctx) → Γ.denote → Γ.denS N
  | [], _ => ()
  | (_, τ) :: Γ, (x, ρ) => (Ty.convInv N I τ x, Ctx.convInv Γ ρ)

/-- A state of the program's types as the denotation's. -/
def Ctx.tupConv : (Γ : Ctx) → Γ.tupS N → Γ.tup
  | [], _ => ()
  | [(_, τ)], x => Ty.conv N I τ x
  | (_, τ) :: _ :: _, (x, t) => (Ty.conv N I τ x, Ctx.tupConv _ t)

/-- The functions of the program's types, as the denotation's: on the denotation's arguments, converted. -/
def Sigs.canon : (Φ : Sigs) → Φ.denS N → Φ.denote
  | [], _ => ()
  | s :: Φ, (g, fs) => (fun c => Ty.conv N I s.result (g (Ctx.convInv N I s.params c)), Sigs.canon Φ fs)

def Sigs.canonSafety : (Φ : Sigs) → Φ.safetyS N → Φ.safety
  | [], _ => ()
  | s :: Φ, (g, ss) => (fun c => g (Ctx.convInv N I s.params c), Sigs.canonSafety Φ ss)

end

end Ariadne

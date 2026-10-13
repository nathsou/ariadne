import V2.Typed.Ty

/-!
# Typed syntax

Intrinsically typed programs whose erasure is exactly the source syntax: one
constructor per source form, plus coercions that are no-ops on JavaScript values
(`widen`). The type checker that builds them is untrusted; per file, the kernel
checks `erase typed = ast`.

- Local variables are typed de Bruijn indices that also carry their name; a
  reference past another binding proves the names differ, so it denotes the
  innermost binding of its name, as the evaluator's lookup does.
- Narrowing (`x == null`, a `switch` on a union's tag) replaces the type of a
  variable in the context, so the environment stays aligned with the context.
- Function references index the signatures of the functions declared earlier,
  newest first.
-/

namespace V2

/-- Bindings in scope, innermost first. -/
abbrev Ctx := List (String × Ty)

abbrev Ctx.denote : Ctx → Type
  | [] => Unit
  | (_, τ) :: Γ => τ.denote × Ctx.denote Γ

/-- A reference to the innermost binding of `x`, of type `τ`. -/
inductive Var : Ctx → String → Ty → Type where
  | here : Var ((x, τ) :: Γ) x τ
  | there : x ≠ y → Var Γ x τ → Var ((y, σ) :: Γ) x τ

def Var.get : Var Γ x τ → Γ.denote → τ.denote
  | .here, (v, _) => v
  | .there _ v, (_, ρ) => v.get ρ

/-- The context with the variable's type replaced by `σ`. -/
def Var.narrow : {Γ : Ctx} → Var Γ x τ → Ty → Ctx
  | (y, _) :: Γ, .here, σ => (y, σ) :: Γ
  | p :: _, .there _ v, σ => p :: v.narrow σ

/-- The environment with the variable's value replaced. -/
def Var.narrowVal : {Γ : Ctx} → (v : Var Γ x τ) → Γ.denote → σ.denote → (v.narrow σ).denote
  | (_, _) :: _, .here, (_, ρ), y => show σ.denote × _ from (y, ρ)
  | (_, τ') :: _, .there _ v, (a, ρ), y => show τ'.denote × _ from (a, v.narrowVal ρ y)

/-- Back to the wide context, embedding the narrowed value. -/
def Var.widen : {Γ : Ctx} → (v : Var Γ x τ) → (σ.denote → τ.denote) → (v.narrow σ).denote → Γ.denote
  | (_, _) :: _, .here, e, ρ => let ρ' : σ.denote × _ := ρ; (e ρ'.1, ρ'.2)
  | (_, τ') :: _, .there _ v, e, ρ => let ρ' : τ'.denote × _ := ρ; (ρ'.1, v.widen e ρ'.2)

/-- Parameters that may be omitted at a call: optionals admitting `undefined`. -/
def Ctx.omittable : Ctx → Bool
  | [] => true
  | (_, .option n _) :: ps => n.undef? && Ctx.omittable ps
  | _ => false

def Ctx.none : (ps : Ctx) → ps.denote
  | [] => ()
  | (_, .option _ _) :: ps => (Option.none, Ctx.none ps)
  | (_, τ) :: ps => (τ.default, Ctx.none ps)

structure Sig where
  name : String
  params : Ctx
  result : Ty
  /-- The function performs no operation that can leave what the model covers, so
  it is safe on every input (checked against its body by `TProgram.WF`). -/
  trivial : Bool := false
  deriving Repr, BEq, Inhabited

abbrev Sig.denote (s : Sig) : Type := s.params.denote → s.result.denote

/-- Signatures of the functions in scope, newest first. -/
abbrev Sigs := List Sig

abbrev Sigs.denote : Sigs → Type
  | [] => Unit
  | s :: Φ => s.denote × Sigs.denote Φ

/-- Each function's safety condition: its arguments keep every operation within
what the model covers (numbers in the safe range, consistent comparators). -/
abbrev Sigs.safety : Sigs → Type
  | [] => Unit
  | s :: Φ => (s.params.denote → Bool) × Sigs.safety Φ

/-- A reference to a function declared earlier. -/
inductive FVar : Sigs → String → Sig → Type where
  | here : FVar (s :: Φ) s.name s
  | there : FVar Φ f t → FVar (s :: Φ) f t

def FVar.get : FVar Φ f s → Φ.denote → s.denote
  | .here, (g, _) => g
  | .there v, (_, fs) => v.get fs

def FVar.safe : FVar Φ f s → Φ.safety → s.params.denote → Bool
  | .here, (g, _) => g
  | .there v, (_, fs) => v.safe fs

/-! ## Record literals -/

/-- How a record literal's type takes its fields from the literal's entries
(`src`, in source order): each field is an entry. -/
inductive Sel (src : Fields) : Fields → Type where
  | nil : Sel src .nil
  | cons (i : FIdx src f τ) (rest : Sel src fs) : Sel src (.cons f τ fs)
  /-- An optional field the literal leaves out: it reads as `undefined`. -/
  | absent (h : (n.undef? && !src.names.contains f) = true) (rest : Sel src fs) : Sel src (.cons f (.option n τ) fs)

/-- How `{ ...r, entries }` takes each field: an entry, or `r`'s field. -/
inductive Upd (src : Fields) : Fields → Type where
  | nil : Upd src .nil
  | set (i : FIdx src f τ) (rest : Upd src fs) : Upd src (.cons f τ fs)
  | keep (h : src.names.contains f = false) (rest : Upd src fs) : Upd src (.cons f τ fs)

/-- Entry names a literal may use: distinct, and none `__proto__`. -/
def Fields.literalNames (fs : Fields) : Bool := distinct fs.names && !fs.names.contains "__proto__"

/-- A union's tags are distinct. -/
def Variants.tags : Variants → List TagLit
  | .one t _ => [t]
  | .cons t _ rest => t :: rest.tags

/-- A union's tags are distinct and all strings or all booleans (so `===` compares
them without faulting). -/
def Variants.tagsOk (vs : Variants) : Bool :=
  (vs.tags.all (·.isStr) || vs.tags.all (!·.isStr)) && distinctTagList vs.tags
where
  distinctTagList : List TagLit → Bool
    | [] => true
    | t :: ts => !ts.contains t && distinctTagList ts

mutual
  inductive TExpr (Φ : Sigs) : Ctx → Ty → Type where
    | bool (b : Bool) : TExpr Φ Γ .bool
    | int (n : Int) : TExpr Φ Γ .int
    | str (s : JSString) : TExpr Φ Γ .string
    | tagLit (t : TagLit) : TExpr Φ Γ (.tag t)
    /-- A string literal of a literal union. -/
    | litIn (a : JSString) (as : List JSString) (i : Fin (as.length + 1)) : TExpr Φ Γ (.lits a as)
    | undef (n : Nullish) (τ : Ty) (h : n.undef? = true) : TExpr Φ Γ (.option n τ)
    | null (n : Nullish) (τ : Ty) (h : n.null? = true) : TExpr Φ Γ (.option n τ)
    | var {x : String} (v : Var Γ x τ) : TExpr Φ Γ τ
    /-- A value of a narrowed type used at the wide type: no source syntax, and no
    change to the JavaScript value. -/
    | widen (N : Narrowing σ τ) (e : TExpr Φ Γ σ) : TExpr Φ Γ τ
    | not (e : TExpr Φ Γ .bool) : TExpr Φ Γ .bool
    | neg (e : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | add (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | sub (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | mul (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | concat (a b : TExpr Φ Γ .string) : TExpr Φ Γ .string
    | eq (h : τ.prim = true) (a b : TExpr Φ Γ τ) : TExpr Φ Γ .bool
    | ne (h : τ.prim = true) (a b : TExpr Φ Γ τ) : TExpr Φ Γ .bool
    | lt (a b : TExpr Φ Γ .int) : TExpr Φ Γ .bool
    | le (a b : TExpr Φ Γ .int) : TExpr Φ Γ .bool
    | gt (a b : TExpr Φ Γ .int) : TExpr Φ Γ .bool
    | ge (a b : TExpr Φ Γ .int) : TExpr Φ Γ .bool
    | slt (a b : TExpr Φ Γ .string) : TExpr Φ Γ .bool
    | sle (a b : TExpr Φ Γ .string) : TExpr Φ Γ .bool
    | sgt (a b : TExpr Φ Γ .string) : TExpr Φ Γ .bool
    | sge (a b : TExpr Φ Γ .string) : TExpr Φ Γ .bool
    | and (a b : TExpr Φ Γ .bool) : TExpr Φ Γ .bool
    | or (a b : TExpr Φ Γ .bool) : TExpr Φ Γ .bool
    | cond (c : TExpr Φ Γ .bool) (a b : TExpr Φ Γ τ) : TExpr Φ Γ τ
    /-- `e == null`. -/
    | isNull (h : τ.nonNullish = true) (e : TExpr Φ Γ (.option n τ)) : TExpr Φ Γ .bool
    /-- `e != null`. -/
    | notNull (h : τ.nonNullish = true) (e : TExpr Φ Γ (.option n τ)) : TExpr Φ Γ .bool
    /-- `x == null ? a : b`, with `x` narrowed in `b`. -/
    | condNull {x : String} (v : Var Γ x (.option n σ)) (h : σ.nonNullish = true)
        (a : TExpr Φ Γ τ) (b : TExpr Φ (v.narrow σ) τ) : TExpr Φ Γ τ
    /-- `x != null ? a : b`, with `x` narrowed in `a`. -/
    | condNotNull {x : String} (v : Var Γ x (.option n σ)) (h : σ.nonNullish = true)
        (a : TExpr Φ (v.narrow σ) τ) (b : TExpr Φ Γ τ) : TExpr Φ Γ τ
    /-- `a ?? b`. -/
    | coalesce (h : τ.nonNullish = true) (a : TExpr Φ Γ (.option n τ)) (b : TExpr Φ Γ τ) : TExpr Φ Γ τ
    /-- `f(args)`, where no local in scope is named `f` (so the call reaches the
    declared function). -/
    | call {f : String} {s : Sig} (fn : FVar Φ f s) (h : (Γ.map Prod.fst).contains f = false)
        (args : TArgs Φ Γ s.params) : TExpr Φ Γ s.result
    /-- `{ f: e, … }`. -/
    | record (es : TEntries Φ Γ src) (sel : Sel src fs) (h : src.literalNames = true) : TExpr Φ Γ (.record fs)
    /-- `{ ...r, f: e, … }`. -/
    | update (r : TExpr Φ Γ (.record fs)) (es : TEntries Φ Γ src) (u : Upd src fs) (h : src.literalNames = true) :
        TExpr Φ Γ (.record fs)
    /-- `e.f`. -/
    | field (e : TExpr Φ Γ (.record fs)) (i : FIdx fs f τ) (h : protoNames.contains f = false) : TExpr Φ Γ τ
    /-- A `number` literal. -/
    | num (n : Int) : TExpr Φ Γ .number
    /-- `-n` for a `number` literal `n`. -/
    | negNum (n : Int) (h : inRange n = true) : TExpr Φ Γ .number
    | nneg (e : TExpr Φ Γ .number) : TExpr Φ Γ .number
    | nadd (a b : TExpr Φ Γ .number) : TExpr Φ Γ .number
    | nsub (a b : TExpr Φ Γ .number) : TExpr Φ Γ .number
    | nmul (a b : TExpr Φ Γ .number) : TExpr Φ Γ .number
    | nlt (a b : TExpr Φ Γ .number) : TExpr Φ Γ .bool
    | nle (a b : TExpr Φ Γ .number) : TExpr Φ Γ .bool
    | ngt (a b : TExpr Φ Γ .number) : TExpr Φ Γ .bool
    | nge (a b : TExpr Φ Γ .number) : TExpr Φ Γ .bool
    /-- `[e, ...a, …]`. -/
    | array (es : TElems Φ Γ τ) : TExpr Φ Γ (.array τ)
    /-- `a.length` on an array. -/
    | length (a : TExpr Φ Γ (.array τ)) : TExpr Φ Γ .number
    /-- `s.length` on a string (UTF-16 code units). -/
    | slength (s : TExpr Φ Γ .string) : TExpr Φ Γ .number
    /-- `a[i]`: `undefined` out of bounds. -/
    | index (a : TExpr Φ Γ (.array τ)) (i : TExpr Φ Γ .number) : TExpr Φ Γ (.option .undef τ)
    /-- `a.includes(x)`. -/
    | includes (h : τ.prim = true) (a : TExpr Φ Γ (.array τ)) (e : TExpr Φ Γ τ) : TExpr Φ Γ .bool
    /-- `a.some((x) => p)`. -/
    | any (a : TExpr Φ Γ (.array τ)) (x : String) (p : TExpr Φ ((x, τ) :: Γ) .bool) : TExpr Φ Γ .bool
    /-- `a.every((x) => p)`. -/
    | all (a : TExpr Φ Γ (.array τ)) (x : String) (p : TExpr Φ ((x, τ) :: Γ) .bool) : TExpr Φ Γ .bool
    /-- `a.find((x) => p)`. -/
    | find (a : TExpr Φ Γ (.array τ)) (x : String) (p : TExpr Φ ((x, τ) :: Γ) .bool) :
        TExpr Φ Γ (.option .undef τ)
    /-- `a.filter((x) => p)`. -/
    | filter (a : TExpr Φ Γ (.array τ)) (x : String) (p : TExpr Φ ((x, τ) :: Γ) .bool) : TExpr Φ Γ (.array τ)
    /-- `a.map((x) => f)`. -/
    | map (a : TExpr Φ Γ (.array τ)) (x : String) (f : TExpr Φ ((x, τ) :: Γ) σ) : TExpr Φ Γ (.array σ)
    /-- `a.toSorted((x, y) => c)`. -/
    | sorted (a : TExpr Φ Γ (.array τ)) (x y : String) (c : TExpr Φ ((x, τ) :: (y, τ) :: Γ) .number) :
        TExpr Φ Γ (.array τ)

  /-- Arguments for the parameters `ps`, evaluated in `Γ`. -/
  inductive TArgs (Φ : Sigs) : Ctx → Ctx → Type where
    | nil : TArgs Φ Γ []
    | cons {x : String} (e : TExpr Φ Γ τ) (rest : TArgs Φ Γ ps) : TArgs Φ Γ ((x, τ) :: ps)
    /-- The remaining parameters are omitted (each is `undefined`). -/
    | omitted (h : ps.omittable = true) : TArgs Φ Γ ps

  /-- A record literal's entries, in source order, with their types. -/
  inductive TEntries (Φ : Sigs) : Ctx → Fields → Type where
    | nil : TEntries Φ Γ .nil
    | cons (f : String) (e : TExpr Φ Γ τ) (rest : TEntries Φ Γ src) : TEntries Φ Γ (.cons f τ src)

  /-- An array literal's elements. -/
  inductive TElems (Φ : Sigs) : Ctx → Ty → Type where
    | nil : TElems Φ Γ τ
    | cons (e : TExpr Φ Γ τ) (rest : TElems Φ Γ τ) : TElems Φ Γ τ
    /-- `...a`. -/
    | spread (a : TExpr Φ Γ (.array τ)) (rest : TElems Φ Γ τ) : TElems Φ Γ τ
end

mutual
  /-- Statement lists of a function returning `τ`, run in `Γ`. A declaration scopes
  over the rest of its list. -/
  inductive TStmts (Φ : Sigs) : Ctx → Ty → Type where
    | nil : TStmts Φ Γ τ
    | const (x : String) (e : TExpr Φ Γ σ) (rest : TStmts Φ ((x, σ) :: Γ) τ) : TStmts Φ Γ τ
    | ret (e : TExpr Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    | ite (c : TExpr Φ Γ .bool) (yes no : TStmts Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    | block (body : TStmts Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    | brk (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    /-- `if (x == null) yes else no`, with `x` narrowed in `no`. -/
    | ifNull {x : String} (v : Var Γ x (.option n σ)) (h : σ.nonNullish = true)
        (yes : TStmts Φ Γ τ) (no : TStmts Φ (v.narrow σ) τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    /-- `if (x == null) yes` where `yes` never completes normally, with `x` narrowed
    in the rest of the list. -/
    | ifNullExit {x : String} (v : Var Γ x (.option n σ)) (h : σ.nonNullish = true)
        (yes : TStmts Φ Γ τ) (rest : TStmts Φ (v.narrow σ) τ) : TStmts Φ Γ τ
    /-- `if (x != null) yes else no`, with `x` narrowed in `yes`. -/
    | ifNotNull {x : String} (v : Var Γ x (.option n σ)) (h : σ.nonNullish = true)
        (yes : TStmts Φ (v.narrow σ) τ) (no : TStmts Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
    /-- `switch (x.key) { case t₁: … }` over a union, one case per variant in the
    union's order, with `x` narrowed to the variant in its case. -/
    | switchU {x key : String} {vs : Variants} (v : Var Γ x (.union key vs))
        (h : (vs.tagsOk && !protoNames.contains key) = true)
        (cases : TCases Φ Γ τ v vs) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ

  /-- The cases of `switchU` for the variants `vs`, a suffix of the union's. -/
  inductive TCases (Φ : Sigs) : (Γ : Ctx) → Ty → {x key : String} → {vs0 : Variants} →
      Var Γ x (.union key vs0) → Variants → Type where
    | one {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {t : TagLit} {fs : Fields}
        {v : Var Γ x (.union key vs0)} (body : TStmts Φ (v.narrow (vrec key t fs)) τ) : TCases Φ Γ τ v (.one t fs)
    | cons {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {t : TagLit} {fs : Fields} {rest : Variants}
        {v : Var Γ x (.union key vs0)} (body : TStmts Φ (v.narrow (vrec key t fs)) τ)
        (more : TCases Φ Γ τ v rest) : TCases Φ Γ τ v (.cons t fs rest)
end

/-- A program: its functions, newest first, each typed against the earlier ones. -/
inductive TProgram : Sigs → Type where
  | nil : TProgram []
  | cons (s : Sig) (body : TStmts Φ s.params s.result) (rest : TProgram Φ) : TProgram (s :: Φ)

/-! ## Erasure -/

def nullTest (x : String) : Expr := .binary .looseEq (.var x) (.lit .null)
def notNullTest (x : String) : Expr := .binary .looseNe (.var x) (.lit .null)

mutual
  def TExpr.erase : TExpr Φ Γ τ → Expr
    | .bool b => .lit (.bool b)
    | .int n => .lit (.bigint n)
    | .str s => .lit (.string s)
    | .tagLit t => .lit t.lit
    | .litIn a as i => .lit (.string ((a :: as)[i]))
    | .undef .. => .lit .undefined
    | .null .. => .lit .null
    | @TExpr.var _ _ _ x _ => .var x
    | .widen _ e => e.erase
    | .not e => .unary .not e.erase
    | .neg e => .unary .neg e.erase
    | .add a b => .binary .add a.erase b.erase
    | .sub a b => .binary .sub a.erase b.erase
    | .mul a b => .binary .mul a.erase b.erase
    | .concat a b => .binary .add a.erase b.erase
    | .eq _ a b => .binary .eq a.erase b.erase
    | .ne _ a b => .binary .ne a.erase b.erase
    | .lt a b | .slt a b => .binary .lt a.erase b.erase
    | .le a b | .sle a b => .binary .le a.erase b.erase
    | .gt a b | .sgt a b => .binary .gt a.erase b.erase
    | .ge a b | .sge a b => .binary .ge a.erase b.erase
    | .and a b => .binary .and a.erase b.erase
    | .or a b => .binary .or a.erase b.erase
    | .cond c a b => .cond c.erase a.erase b.erase
    | .isNull _ e => .binary .looseEq e.erase (.lit .null)
    | .notNull _ e => .binary .looseNe e.erase (.lit .null)
    | @TExpr.condNull _ _ _ _ _ x _ _ a b => .cond (nullTest x) a.erase b.erase
    | @TExpr.condNotNull _ _ _ _ _ x _ _ a b => .cond (notNullTest x) a.erase b.erase
    | .coalesce _ a b => .binary .coalesce a.erase b.erase
    | @TExpr.call _ _ f _ _ _ args => .call f args.erase
    | .record es _ _ => .record es.erase
    | .update r es _ _ => .record ((none, r.erase) :: es.erase)
    | @TExpr.field _ _ _ f _ e _ _ => .field e.erase f
    | .num n => .lit (.number n)
    | .negNum n _ => .unary .neg (.lit (.number n))
    | .nneg e => .unary .neg e.erase
    | .nadd a b => .binary .add a.erase b.erase
    | .nsub a b => .binary .sub a.erase b.erase
    | .nmul a b => .binary .mul a.erase b.erase
    | .nlt a b => .binary .lt a.erase b.erase
    | .nle a b => .binary .le a.erase b.erase
    | .ngt a b => .binary .gt a.erase b.erase
    | .nge a b => .binary .ge a.erase b.erase
    | .array es => .array es.erase
    | .length a => .field a.erase "length"
    | .slength s => .field s.erase "length"
    | .index a i => .index a.erase i.erase
    | .includes _ a e => .method a.erase "includes" [e.erase]
    | .any a x p => .method a.erase "some" [.arrow [x] p.erase]
    | .all a x p => .method a.erase "every" [.arrow [x] p.erase]
    | .find a x p => .method a.erase "find" [.arrow [x] p.erase]
    | .filter a x p => .method a.erase "filter" [.arrow [x] p.erase]
    | .map a x f => .method a.erase "map" [.arrow [x] f.erase]
    | .sorted a x y c => .method a.erase "toSorted" [.arrow [x, y] c.erase]

  def TArgs.erase : TArgs Φ Γ ps → List Expr
    | .nil => []
    | .cons e rest => e.erase :: rest.erase
    | .omitted _ => []

  def TEntries.erase : TEntries Φ Γ src → List (Option String × Expr)
    | .nil => []
    | .cons f e rest => (some f, e.erase) :: rest.erase

  def TElems.erase : TElems Φ Γ τ → List (Bool × Expr)
    | .nil => []
    | .cons e rest => (false, e.erase) :: rest.erase
    | .spread a rest => (true, a.erase) :: rest.erase
end

mutual
  def TStmts.erase : TStmts Φ Γ τ → List Stmt
    | .nil => []
    | .const x e rest => .const x e.erase :: rest.erase
    | .ret e rest => .ret e.erase :: rest.erase
    | .ite c yes no rest => .ite c.erase yes.erase no.erase :: rest.erase
    | .block body rest => .block body.erase :: rest.erase
    | .brk rest => .brk :: rest.erase
    | @TStmts.ifNull _ _ _ _ _ x _ _ yes no rest => .ite (nullTest x) yes.erase no.erase :: rest.erase
    | @TStmts.ifNullExit _ _ _ _ _ x _ _ yes rest => .ite (nullTest x) yes.erase [] :: rest.erase
    | @TStmts.ifNotNull _ _ _ _ _ x _ _ yes no rest => .ite (notNullTest x) yes.erase no.erase :: rest.erase
    | @TStmts.switchU _ _ _ x key _ _ _ cases rest => .switch (.field (.var x) key) cases.erase :: rest.erase

  def TCases.erase {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → List (Option Expr × List Stmt)
    | .one (t := t) body => [(some (.lit t.lit), body.erase)]
    | .cons (t := t) body more => (some (.lit t.lit), body.erase) :: more.erase
end

/-- Functions in source order (oldest first). -/
def TProgram.erase : TProgram Φ → Program
  | .nil => []
  | .cons s body rest => rest.erase ++ [{ name := s.name, params := s.params.map Prod.fst, body := body.erase }]

/-! ## Control flow

Conservative facts about how a statement list can end, used to rule out outcomes
in the proof: whether it may complete normally (fall through), `break`, or
`continue`. -/

mutual
  def TStmts.falls : TStmts Φ Γ τ → Bool
    | .nil => true
    | .const _ _ rest => rest.falls
    | .ret _ _ => false
    | .ite _ yes no rest | .ifNull _ _ yes no rest | .ifNotNull _ _ yes no rest =>
      (yes.falls || no.falls) && rest.falls
    | .block body rest => body.falls && rest.falls
    | .brk _ => false
    | .ifNullExit _ _ _ rest => rest.falls
    | .switchU _ _ cases rest => (cases.falls || cases.breaks) && rest.falls

  def TStmts.breaks : TStmts Φ Γ τ → Bool
    | .nil => false
    | .const _ _ rest => rest.breaks
    | .ret _ _ => false
    | .ite _ yes no rest | .ifNull _ _ yes no rest | .ifNotNull _ _ yes no rest =>
      yes.breaks || no.breaks || ((yes.falls || no.falls) && rest.breaks)
    | .block body rest => body.breaks || (body.falls && rest.breaks)
    | .brk _ => true
    | .ifNullExit _ _ yes rest => yes.breaks || rest.breaks
    | .switchU _ _ cases rest => (cases.falls || cases.breaks) && rest.breaks

  def TStmts.continues : TStmts Φ Γ τ → Bool
    | .nil => false
    | .const _ _ rest => rest.continues
    | .ret _ _ => false
    | .ite _ yes no rest | .ifNull _ _ yes no rest | .ifNotNull _ _ yes no rest =>
      yes.continues || no.continues || ((yes.falls || no.falls) && rest.continues)
    | .block body rest => body.continues || (body.falls && rest.continues)
    | .brk _ => false
    | .ifNullExit _ _ yes rest => yes.continues || rest.continues
    | .switchU _ _ cases rest => cases.continues || ((cases.falls || cases.breaks) && rest.continues)

  /-- Whether the cases are well formed: every case but the last cannot complete
  normally. Also whether a case may fall off the end of the switch. -/
  def TCases.falls {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → Bool
    | .one body => body.falls
    | .cons _ more => more.falls

  def TCases.breaks {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → Bool
    | .one body => body.breaks
    | .cons body more => body.breaks || more.breaks

  def TCases.continues {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → Bool
    | .one body => body.continues
    | .cons body more => body.continues || more.continues

  /-- No case but the last falls through, and no `ifNullExit` branch completes
  normally. -/
  def TStmts.wf : TStmts Φ Γ τ → Bool
    | .nil => true
    | .const _ _ rest | .ret _ rest | .brk rest => rest.wf
    | .ite _ yes no rest | .ifNull _ _ yes no rest | .ifNotNull _ _ yes no rest => yes.wf && no.wf && rest.wf
    | .block body rest => body.wf && rest.wf
    | .ifNullExit _ _ yes rest => !yes.falls && yes.wf && rest.wf
    | .switchU _ _ cases rest => cases.wf && rest.wf

  def TCases.wf {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → Bool
    | .one body => body.wf
    | .cons body more => !body.falls && body.wf && more.wf
end

/-! ## Trivially safe syntax

No operation that can leave what the model covers, and calls only to trivially
safe functions. -/

mutual
  def TExpr.trivial : TExpr Φ Γ τ → Bool
    | .bool _ | .int _ | .str _ | .tagLit _ | .litIn .. | .undef .. | .null .. | .var _ => true
    | .widen _ e | .not e | .neg e | .isNull _ e | .notNull _ e | .field e _ _ => e.trivial
    | .add a b | .sub a b | .mul a b | .concat a b | .eq _ a b | .ne _ a b | .lt a b | .le a b | .gt a b
    | .ge a b | .slt a b | .sle a b | .sgt a b | .sge a b | .and a b | .or a b | .coalesce _ a b =>
      a.trivial && b.trivial
    | .cond c a b => c.trivial && a.trivial && b.trivial
    | .condNull _ _ a b | .condNotNull _ _ a b => a.trivial && b.trivial
    | @TExpr.call _ _ _ s _ _ args => s.trivial && args.trivial
    | .record es _ _ => es.trivial
    | .update r es _ _ => r.trivial && es.trivial
    | .num _ | .negNum .. => true
    | .nneg _ | .nadd .. | .nsub .. | .nmul .. | .sorted .. => false
    | .nlt a b | .nle a b | .ngt a b | .nge a b | .index a b => a.trivial && b.trivial
    | .includes _ a e => a.trivial && e.trivial
    | .any a _ p | .all a _ p | .find a _ p | .filter a _ p | .map a _ p => a.trivial && p.trivial
    | .array es => es.trivial
    | .length e | .slength e => e.trivial

  def TArgs.trivial : TArgs Φ Γ ps → Bool
    | .nil | .omitted _ => true
    | .cons e rest => e.trivial && rest.trivial

  def TEntries.trivial : TEntries Φ Γ src → Bool
    | .nil => true
    | .cons _ e rest => e.trivial && rest.trivial

  def TElems.trivial : TElems Φ Γ τ → Bool
    | .nil => true
    | .cons e rest | .spread e rest => e.trivial && rest.trivial
end

mutual
  def TStmts.trivial : TStmts Φ Γ τ → Bool
    | .nil => true
    | .const _ e rest | .ret e rest => e.trivial && rest.trivial
    | .ite c yes no rest => c.trivial && yes.trivial && no.trivial && rest.trivial
    | .block body rest => body.trivial && rest.trivial
    | .brk rest => rest.trivial
    | .ifNull _ _ yes no rest | .ifNotNull _ _ yes no rest => yes.trivial && no.trivial && rest.trivial
    | .ifNullExit _ _ yes rest => yes.trivial && rest.trivial
    | .switchU _ _ cases rest => cases.trivial && rest.trivial

  def TCases.trivial {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} {vs : Variants} : TCases Φ Γ τ v vs → Bool
    | .one body => body.trivial
    | .cons body more => body.trivial && more.trivial
end

def TProgram.names : TProgram Φ → List String
  | .nil => []
  | .cons s _ rest => s.name :: rest.names

/-- Every body is well formed, returns on every path, and has no `break` or
`continue` outside a loop or `switch`. -/
def TProgram.bodiesOk : TProgram Φ → Bool
  | .nil => true
  | .cons s body rest => body.wf && !body.falls && !body.breaks && !body.continues &&
      (!s.trivial || body.trivial) && rest.bodiesOk

end V2

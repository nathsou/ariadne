import V2.Model.Eval

/-!
# Typed syntax

Intrinsically typed programs whose erasure is exactly the source syntax: one
constructor per source form. The type checker that builds them is untrusted;
per file, the kernel checks `erase typed = ast`.

- Local variables are typed de Bruijn indices that also carry their name; a
  reference past another binding proves the names differ, so it denotes the
  innermost binding of its name, as JavaScript scoping does.
- Function references index the signatures of the functions declared earlier,
  newest first. Function names are distinct (checked in `TProgram.wf`).
-/

namespace V2

inductive Ty where
  | bool | int | string
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Ty.denote : Ty → Type
  | .bool => Bool
  | .int => Int
  | .string => JSString

def Ty.default : (τ : Ty) → τ.denote
  | .bool => false
  | .int => 0
  | .string => []

def Ty.encode : (τ : Ty) → τ.denote → JSValue
  | .bool, b => .bool b
  | .int, n => .bigint n
  | .string, s => .string s

/-- Bindings in scope, innermost first. -/
abbrev Ctx := List (String × Ty)

abbrev Ctx.denote : Ctx → Type
  | [] => Unit
  | (_, τ) :: Γ => τ.denote × Ctx.denote Γ

/-- The model's environment for typed bindings. -/
def Ctx.toEnv : (Γ : Ctx) → Γ.denote → Env
  | [], () => []
  | (x, τ) :: Γ, (v, ρ) => (x, τ.encode v) :: Ctx.toEnv Γ ρ

/-- Argument values, in parameter order. -/
def Ctx.encode : (Γ : Ctx) → Γ.denote → List JSValue
  | [], () => []
  | (_, τ) :: Γ, (v, ρ) => τ.encode v :: Ctx.encode Γ ρ

/-- A reference to the innermost binding of `x`, of type `τ`. -/
inductive Var : Ctx → String → Ty → Type where
  | here : Var ((x, τ) :: Γ) x τ
  | there : x ≠ y → Var Γ x τ → Var ((y, σ) :: Γ) x τ

def Var.get : Var Γ x τ → Γ.denote → τ.denote
  | .here, (v, _) => v
  | .there _ v, (_, ρ) => v.get ρ

structure Sig where
  name : String
  params : Ctx
  result : Ty
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Sig.denote (s : Sig) : Type := s.params.denote → s.result.denote

/-- Signatures of the functions in scope, newest first. -/
abbrev Sigs := List Sig

abbrev Sigs.denote : Sigs → Type
  | [] => Unit
  | s :: Φ => s.denote × Sigs.denote Φ

/-- A reference to a function declared earlier. -/
inductive FVar : Sigs → String → Sig → Type where
  | here : FVar (s :: Φ) s.name s
  | there : FVar Φ f t → FVar (s :: Φ) f t

def FVar.get : FVar Φ f s → Φ.denote → s.denote
  | .here, (g, _) => g
  | .there v, (_, fs) => v.get fs

mutual
  inductive TExpr (Φ : Sigs) : Ctx → Ty → Type where
    | bool (b : Bool) : TExpr Φ Γ .bool
    | int (n : Int) : TExpr Φ Γ .int
    | str (s : JSString) : TExpr Φ Γ .string
    | var {x : String} (v : Var Γ x τ) : TExpr Φ Γ τ
    | not (e : TExpr Φ Γ .bool) : TExpr Φ Γ .bool
    | neg (e : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | add (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | sub (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | mul (a b : TExpr Φ Γ .int) : TExpr Φ Γ .int
    | concat (a b : TExpr Φ Γ .string) : TExpr Φ Γ .string
    | eq (a b : TExpr Φ Γ τ) : TExpr Φ Γ .bool
    | ne (a b : TExpr Φ Γ τ) : TExpr Φ Γ .bool
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
    | call {f : String} {s : Sig} (fn : FVar Φ f s) (args : TArgs Φ Γ s.params) : TExpr Φ Γ s.result

  /-- Arguments for the parameters `ps`, evaluated in `Γ`. -/
  inductive TArgs (Φ : Sigs) : Ctx → Ctx → Type where
    | nil : TArgs Φ Γ []
    | cons {x : String} (e : TExpr Φ Γ τ) (rest : TArgs Φ Γ ps) : TArgs Φ Γ ((x, τ) :: ps)
end

/-- Statement lists of a function returning `τ`, run in `Γ`. A declaration scopes
over the rest of its list. -/
inductive TStmts (Φ : Sigs) : Ctx → Ty → Type where
  | nil : TStmts Φ Γ τ
  | const (x : String) (e : TExpr Φ Γ σ) (rest : TStmts Φ ((x, σ) :: Γ) τ) : TStmts Φ Γ τ
  | ret (e : TExpr Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ
  | ite (c : TExpr Φ Γ .bool) (yes no : TStmts Φ Γ τ) (rest : TStmts Φ Γ τ) : TStmts Φ Γ τ

/-- A program: its functions, newest first, each typed against the earlier ones. -/
inductive TProgram : Sigs → Type where
  | nil : TProgram []
  | cons (s : Sig) (body : TStmts Φ s.params s.result) (rest : TProgram Φ) : TProgram (s :: Φ)

/-! ## Erasure -/

mutual
  def TExpr.erase : TExpr Φ Γ τ → Expr
    | .bool b => .lit (.bool b)
    | .int n => .lit (.bigint n)
    | .str s => .lit (.string s)
    | @TExpr.var _ _ _ x _ => .var x
    | .not e => .unary .not e.erase
    | .neg e => .unary .neg e.erase
    | .add a b => .binary .add a.erase b.erase
    | .sub a b => .binary .sub a.erase b.erase
    | .mul a b => .binary .mul a.erase b.erase
    | .concat a b => .binary .add a.erase b.erase
    | .eq a b => .binary .eq a.erase b.erase
    | .ne a b => .binary .ne a.erase b.erase
    | .lt a b | .slt a b => .binary .lt a.erase b.erase
    | .le a b | .sle a b => .binary .le a.erase b.erase
    | .gt a b | .sgt a b => .binary .gt a.erase b.erase
    | .ge a b | .sge a b => .binary .ge a.erase b.erase
    | .and a b => .binary .and a.erase b.erase
    | .or a b => .binary .or a.erase b.erase
    | .cond c a b => .cond c.erase a.erase b.erase
    | @TExpr.call _ _ f _ _ args => .call f args.erase

  def TArgs.erase : TArgs Φ Γ ps → List Expr
    | .nil => []
    | .cons e rest => e.erase :: rest.erase
end

def TStmts.erase : TStmts Φ Γ τ → List Stmt
  | .nil => []
  | .const x e rest => .const x e.erase :: rest.erase
  | .ret e rest => .ret e.erase :: rest.erase
  | .ite c yes no rest => .ite c.erase yes.erase no.erase :: rest.erase

/-- Functions in source order (oldest first). -/
def TProgram.erase : TProgram Φ → Program
  | .nil => []
  | .cons s body rest => rest.erase ++ [{ name := s.name, params := s.params.map Prod.fst, body := body.erase }]

/-! ## Well-formedness -/

/-- Every path through the list ends in a `return`. -/
def TStmts.returns : TStmts Φ Γ τ → Bool
  | .nil => false
  | .const _ _ rest => rest.returns
  | .ret _ _ => true
  | .ite _ yes no rest => (yes.returns && no.returns) || rest.returns

def TProgram.names : TProgram Φ → List String
  | .nil => []
  | .cons s _ rest => s.name :: rest.names

def TProgram.returns : TProgram Φ → Bool
  | .nil => true
  | .cons _ body rest => body.returns && rest.returns

end V2

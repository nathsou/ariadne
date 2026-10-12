import Ariadne.Value
import Ariadne.Shallow.Prelude.Loop

namespace Ariadne.Shallow.Core

/-- Intrinsic types of the first extraction fragment. Additional source types
are refused by elaboration until their native representation is implemented. -/
inductive Ty where
  | unit | bool | int | number | string
  | option (value : Ty)
  | list (element : Ty)
  | pair (left right : Ty)
  | fn (argument result : Ty)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev Ty.denote : Ty → Type
  | .unit => Unit
  | .bool => Bool
  | .int => Int
  | .number => Float.Model
  | .string => JSString
  | .option t => Option t.denote
  | .list t => List t.denote
  | .pair a b => a.denote × b.denote
  | .fn a b => a.denote → b.denote

abbrev Env : List Ty → Type
  | [] => Unit
  | t :: ts => t.denote × Env ts

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: ts) t
  | there : Var ts t → Var (s :: ts) t
  deriving Repr

def Var.get : Var ts t → Env ts → t.denote
  | .here, env => env.1
  | .there v, env => v.get env.2

inductive Unary : Ty → Ty → Type where
  | not : Unary .bool .bool
  | intNeg : Unary .int .int
  | numNeg : Unary .number .number
  | isSome : Unary (.option t) .bool
  deriving Repr

inductive Binary : Ty → Ty → Ty → Type where
  | intAdd : Binary .int .int .int
  | intSub : Binary .int .int .int
  | intMul : Binary .int .int .int
  | intEq : Binary .int .int .bool
  | intLt : Binary .int .int .bool
  | intLe : Binary .int .int .bool
  | numAdd : Binary .number .number .number
  | numSub : Binary .number .number .number
  | numMul : Binary .number .number .number
  | numDiv : Binary .number .number .number
  | numMod : Binary .number .number .number
  | numEq : Binary .number .number .bool
  | numLt : Binary .number .number .bool
  | numLe : Binary .number .number .bool
  | strAppend : Binary .string .string .string
  | strEq : Binary .string .string .bool
  | strLt : Binary .string .string .bool
  | strLe : Binary .string .string .bool
  | boolEq : Binary .bool .bool .bool
  | and : Binary .bool .bool .bool
  | or : Binary .bool .bool .bool
  deriving Repr

/-- Every term is well typed by construction. There are no dynamic value tags,
heaps, cells, or evaluation budgets in its denotation. -/
inductive Term : List Ty → Ty → Type where
  | var : Var Γ t → Term Γ t
  | unit : Term Γ .unit
  | bool : Bool → Term Γ .bool
  | int : Int → Term Γ .int
  | number : Nat → Int → Term Γ .number
  | string : JSString → Term Γ .string
  | unary : Unary a b → Term Γ a → Term Γ b
  | binary : Binary a b c → Term Γ a → Term Γ b → Term Γ c
  | let_ : String → Term Γ a → Term (a :: Γ) b → Term Γ b
  | ite : Term Γ .bool → Term Γ t → Term Γ t → Term Γ t
  | none : Term Γ (.option t)
  | some : Term Γ t → Term Γ (.option t)
  | optionCase : Term Γ (.option a) → Term Γ b → Term (a :: Γ) b → Term Γ b
  | nil : Term Γ (.list t)
  | cons : Term Γ t → Term Γ (.list t) → Term Γ (.list t)
  | pair : Term Γ a → Term Γ b → Term Γ (.pair a b)
  | fst : Term Γ (.pair a b) → Term Γ a
  | snd : Term Γ (.pair a b) → Term Γ b
  | lam : String → Term (a :: Γ) b → Term Γ (.fn a b)
  | app : Term Γ (.fn a b) → Term Γ a → Term Γ b
  | closed : Term [] t → Term Γ t
  deriving Repr

abbrev Renaming (Γ Δ : List Ty) := ∀ {t}, Var Γ t → Var Δ t

def Renaming.lift (r : Renaming Γ Δ) : Renaming (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def Term.rename (r : Renaming Γ Δ) : Term Γ t → Term Δ t
  | .var v => .var (r v)
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .number m e => .number m e
  | .string s => .string s
  | .unary op a => .unary op (a.rename r)
  | .binary op a b => .binary op (a.rename r) (b.rename r)
  | .let_ name a b => .let_ name (a.rename r) (b.rename r.lift)
  | .ite c a b => .ite (c.rename r) (a.rename r) (b.rename r)
  | .none => .none
  | .some a => .some (a.rename r)
  | .optionCase a b c => .optionCase (a.rename r) (b.rename r) (c.rename r.lift)
  | .nil => .nil
  | .cons a b => .cons (a.rename r) (b.rename r)
  | .pair a b => .pair (a.rename r) (b.rename r)
  | .fst a => .fst (a.rename r)
  | .snd a => .snd (a.rename r)
  | .lam name body => .lam name (body.rename r.lift)
  | .app f a => .app (f.rename r) (a.rename r)
  | .closed body => .closed body

abbrev Substitution (Γ Δ : List Ty) := ∀ {t}, Var Γ t → Term Δ t

def Substitution.lift (s : Substitution Γ Δ) : Substitution (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => (s v).rename Var.there

def Term.substitute (s : Substitution Γ Δ) : Term Γ t → Term Δ t
  | .var v => s v
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .number m e => .number m e
  | .string xs => .string xs
  | .unary op a => .unary op (a.substitute s)
  | .binary op a b => .binary op (a.substitute s) (b.substitute s)
  | .let_ name a b => .let_ name (a.substitute s) (b.substitute s.lift)
  | .ite c a b => .ite (c.substitute s) (a.substitute s) (b.substitute s)
  | .none => .none
  | .some a => .some (a.substitute s)
  | .optionCase a b c => .optionCase (a.substitute s) (b.substitute s) (c.substitute s.lift)
  | .nil => .nil
  | .cons a b => .cons (a.substitute s) (b.substitute s)
  | .pair a b => .pair (a.substitute s) (b.substitute s)
  | .fst a => .fst (a.substitute s)
  | .snd a => .snd (a.substitute s)
  | .lam name body => .lam name (body.substitute s.lift)
  | .app f a => .app (f.substitute s) (a.substitute s)
  | .closed body => .closed body

def environmentType : List Ty → Ty
  | [] => .unit
  | t :: ts => .pair t (environmentType ts)

def project (tuple : Term Δ (environmentType Γ)) (v : Var Γ t) : Term Δ t :=
  match v with
  | .here => .fst tuple
  | .there v => project (.snd tuple) v

/-- Abstract all live locals into a tuple. Used for a shared branch continuation. -/
def Term.abstract (body : Term Γ t) : Term Δ (.fn (environmentType Γ) t) :=
  let closed : Term [] (.fn (environmentType Γ) t) :=
    .lam "state" (body.substitute (fun {_} v => project (.var .here) v))
  .closed closed

structure Function where
  params : List Ty
  result : Ty
  body : Term params result

end Ariadne.Shallow.Core

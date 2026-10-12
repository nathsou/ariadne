import Ariadne.Value
import Ariadne.Shallow.Prelude.Loop
import Ariadne.Shallow.Prelude.Array
import Ariadne.Shallow.Named

namespace Ariadne.Shallow.Core

/-- Intrinsic types of the first extraction fragment. Additional source types
are refused by elaboration until their native representation is implemented. -/
inductive Ty where
  | unit | bool | int | number | string
  | option (value : Ty)
  | list (element : Ty)
  | map (key : Key) (value : Ty)
  | set (key : Key)
  | pair (left right : Ty)
  | sum (left right : Ty)
  | named (declaration : Named.Declaration)
  | fn (argument result : Ty)
  | step (state result : Ty)
  | exit (state result : Ty)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev Key.type : Key → Ty
  | .int => .int
  | .number => .number
  | .string => .string
  | .bool => .bool

abbrev Ty.denote (t : Ty) (interp : Named.Interp := Named.canonical) : Type :=
  match t with
  | .unit => Unit
  | .bool => Bool
  | .int => Int
  | .number => Float.Model
  | .string => JSString
  | .option t => Option (t.denote interp)
  | .list t => List (t.denote interp)
  | .map k v => k.Map (v.denote interp)
  | .set k => k.Set
  | .pair a b => a.denote interp × b.denote interp
  | .sum a b => Sum (a.denote interp) (b.denote interp)
  | .named declaration => (interp declaration).Native
  | .fn a b => a.denote interp → b.denote interp
  | .step s r => Step (s.denote interp) (r.denote interp)
  | .exit s r => Exit (s.denote interp) (r.denote interp)

abbrev Env (types : List Ty) (interp : Named.Interp := Named.canonical) : Type :=
  match types with
  | [] => Unit
  | t :: ts => t.denote interp × Env ts interp

def shapeType : Named.Shape → Ty
  | .unit => .unit
  | .bool => .bool
  | .int => .int
  | .number => .number
  | .string => .string
  | .option t => .option (shapeType t)
  | .list t => .list (shapeType t)
  | .map k v => .map k (shapeType v)
  | .set k => .set k
  | .pair a b => .pair (shapeType a) (shapeType b)
  | .sum a b => .sum (shapeType a) (shapeType b)

theorem shape_denote (shape : Named.Shape) (interp : Named.Interp) :
    (shapeType shape).denote interp = shape.denote := by
  induction shape <;> simp_all [shapeType, Ty.denote, Named.Shape.denote]

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: ts) t
  | there : Var ts t → Var (s :: ts) t
  deriving Repr

def Var.get {interp : Named.Interp} : Var ts t → Env ts interp → t.denote interp
  | .here, env => env.1
  | .there v, env => v.get (interp := interp) env.2

inductive Unary : Ty → Ty → Type where
  | not : Unary .bool .bool
  | intNeg : Unary .int .int
  | numNeg : Unary .number .number
  | isSome : Unary (.option t) .bool
  | length : Unary (.list t) .number
  | reverse : Unary (.list t) (.list t)
  | mapSize : Unary (.map k v) .number
  | mapKeys : Unary (.map k v) (.list k.type)
  | mapValues : Unary (.map k v) (.list v)
  | mapEntries : Unary (.map k v) (.list (.pair k.type v))
  | setSize : Unary (.set k) .number
  | setValues : Unary (.set k) (.list k.type)
  | setEntries : Unary (.set k) (.list (.pair k.type k.type))
  deriving Repr

inductive Binary : Ty → Ty → Ty → Type where
  | intAdd : Binary .int .int .int
  | intSub : Binary .int .int .int
  | intMul : Binary .int .int .int
  | intEq : Binary .int .int .bool
  | intLt : Binary .int .int .bool
  | intLe : Binary .int .int .bool
  | intRange : Binary .int .int (.list .int)
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
  | append : Binary (.list t) (.list t) (.list t)
  | get : Binary (.list t) .number (.option t)
  | mapGet : Binary (.map k v) k.type (.option v)
  | mapHas : Binary (.map k v) k.type .bool
  | mapDelete : Binary (.map k v) k.type (.map k v)
  | setHas : Binary (.set k) k.type .bool
  | setAdd : Binary (.set k) k.type (.set k)
  | setDelete : Binary (.set k) k.type (.set k)
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
  | inl : Term Γ a → Term Γ (.sum a b)
  | inr : Term Γ b → Term Γ (.sum a b)
  | sumCase : Term Γ (.sum a b) → Term (a :: Γ) c → Term (b :: Γ) c → Term Γ c
  | pack (declaration : Named.Declaration) : Term Γ (shapeType declaration.shape) → Term Γ (.named declaration)
  | unpack : Term Γ (.named declaration) → Term Γ (shapeType declaration.shape)
  | lam : String → Term (a :: Γ) b → Term Γ (.fn a b)
  | app : Term Γ (.fn a b) → Term Γ a → Term Γ b
  | closed : Term [] t → Term Γ t
  | listMap : Term Γ (.fn a (.fn .number b)) → Term Γ (.list a) → Term Γ (.list b)
  | listFilter : Term Γ (.fn a (.fn .number .bool)) → Term Γ (.list a) → Term Γ (.list a)
  | listReduce : Term Γ (.fn b (.fn a (.fn .number b))) → Term Γ b → Term Γ (.list a) → Term Γ b
  | listSome : Term Γ (.fn a (.fn .number .bool)) → Term Γ (.list a) → Term Γ .bool
  | listEvery : Term Γ (.fn a (.fn .number .bool)) → Term Γ (.list a) → Term Γ .bool
  | listFind : Term Γ (.fn a (.fn .number .bool)) → Term Γ (.list a) → Term Γ (.option a)
  | listFindIndex : Term Γ (.fn a (.fn .number .bool)) → Term Γ (.list a) → Term Γ .number
  | listSlice : Term Γ (.list a) → Term Γ .number → Term Γ .number → Term Γ (.list a)
  | mapEmpty : Term Γ (.map k v)
  | mapSet : Term Γ (.map k v) → Term Γ k.type → Term Γ v → Term Γ (.map k v)
  | setEmpty : Term Γ (.set k)
  | next : Term Γ s → Term Γ (.step s r)
  | stop : Term Γ s → Term Γ (.step s r)
  | ret : Term Γ r → Term Γ (.step s r)
  | each : Term Γ (.list a) → Term Γ s → Term Γ (.fn a (.fn s (.step s r))) → Term Γ (.exit s r)
  | exitCase : Term Γ (.exit s r) → Term Γ (.fn s t) → Term Γ (.fn r t) → Term Γ t
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
  | .inl a => .inl (a.rename r)
  | .inr a => .inr (a.rename r)
  | .unpack a => .unpack (a.rename r)
  | .sumCase a b c => .sumCase (a.rename r) (b.rename r.lift) (c.rename r.lift)
  | .pack d a => .pack d (a.rename r)
  | .lam name body => .lam name (body.rename r.lift)
  | .app f a => .app (f.rename r) (a.rename r)
  | .closed body => .closed body
  | .listMap f xs => .listMap (f.rename r) (xs.rename r)
  | .listFilter f xs => .listFilter (f.rename r) (xs.rename r)
  | .listReduce f a xs => .listReduce (f.rename r) (a.rename r) (xs.rename r)
  | .listSome f xs => .listSome (f.rename r) (xs.rename r)
  | .listEvery f xs => .listEvery (f.rename r) (xs.rename r)
  | .listFind f xs => .listFind (f.rename r) (xs.rename r)
  | .listFindIndex f xs => .listFindIndex (f.rename r) (xs.rename r)
  | .listSlice xs a b => .listSlice (xs.rename r) (a.rename r) (b.rename r)
  | .mapEmpty => .mapEmpty
  | .setEmpty => .setEmpty
  | .mapSet m k v => .mapSet (m.rename r) (k.rename r) (v.rename r)
  | .next a => .next (a.rename r)
  | .stop a => .stop (a.rename r)
  | .ret a => .ret (a.rename r)
  | .each a b c => .each (a.rename r) (b.rename r) (c.rename r)
  | .exitCase a b c => .exitCase (a.rename r) (b.rename r) (c.rename r)

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
  | .inl a => .inl (a.substitute s)
  | .inr a => .inr (a.substitute s)
  | .unpack a => .unpack (a.substitute s)
  | .sumCase a b c => .sumCase (a.substitute s) (b.substitute s.lift) (c.substitute s.lift)
  | .pack d a => .pack d (a.substitute s)
  | .lam name body => .lam name (body.substitute s.lift)
  | .app f a => .app (f.substitute s) (a.substitute s)
  | .closed body => .closed body
  | .listMap f xs => .listMap (f.substitute s) (xs.substitute s)
  | .listFilter f xs => .listFilter (f.substitute s) (xs.substitute s)
  | .listReduce f a xs => .listReduce (f.substitute s) (a.substitute s) (xs.substitute s)
  | .listSome f xs => .listSome (f.substitute s) (xs.substitute s)
  | .listEvery f xs => .listEvery (f.substitute s) (xs.substitute s)
  | .listFind f xs => .listFind (f.substitute s) (xs.substitute s)
  | .listFindIndex f xs => .listFindIndex (f.substitute s) (xs.substitute s)
  | .listSlice xs a b => .listSlice (xs.substitute s) (a.substitute s) (b.substitute s)
  | .mapEmpty => .mapEmpty
  | .setEmpty => .setEmpty
  | .mapSet m k v => .mapSet (m.substitute s) (k.substitute s) (v.substitute s)
  | .next a => .next (a.substitute s)
  | .stop a => .stop (a.substitute s)
  | .ret a => .ret (a.substitute s)
  | .each a b c => .each (a.substitute s) (b.substitute s) (c.substitute s)
  | .exitCase a b c => .exitCase (a.substitute s) (b.substitute s) (c.substitute s)

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

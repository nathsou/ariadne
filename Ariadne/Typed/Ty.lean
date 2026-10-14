import Ariadne.Model.Eval

/-!
# Types, their denotations, and representation

`Ty.Rep τ v x`: the JavaScript value `v` represents the Lean value `x`. It is a
relation, not an encoding: a record is any object whose fields, read as JavaScript
reads them (a missing field is `undefined`), represent the record's fields, in
any order and with any extra fields; an optional is `undefined` or `null` as its
type allows.
-/

namespace Ariadne

/-- Which nullish values encode `none` in an optional type. -/
inductive Nullish where
  /-- `T | undefined`, `x?: T`. -/
  | undef
  /-- `T | null`. -/
  | null
  /-- `T | null | undefined`. -/
  | both
  deriving Repr, BEq, DecidableEq, Inhabited

def Nullish.admits : Nullish → JSValue → Prop
  | .undef, v => v = .undefined
  | .null, v => v = .null
  | .both, v => v = .undefined ∨ v = .null

def Nullish.undef? : Nullish → Bool
  | .null => false
  | _ => true

def Nullish.null? : Nullish → Bool
  | .undef => false
  | _ => true

/-- A literal type's value: a union tag. -/
inductive TagLit where
  | str (s : JSString)
  | bool (b : Bool)
  deriving Repr, DecidableEq, Inhabited

def TagLit.value : TagLit → JSValue
  | .str s => .string s
  | .bool b => .bool b

def TagLit.isStr : TagLit → Bool
  | .str _ => true
  | .bool _ => false

def TagLit.lit : TagLit → Lit
  | .str s => .string s
  | .bool b => .bool b

mutual
  inductive Ty where
    | bool
    /-- `bigint`. -/
    | int
    /-- `number`, in integer mode. -/
    | number
    | string
    /-- A singleton literal type, such as a union's tag. -/
    | tag (t : TagLit)
    /-- A union of string literals. -/
    | lits (first : JSString) (rest : List JSString)
    | option (n : Nullish) (τ : Ty)
    | record (fs : Fields)
    /-- A union of records told apart by the literal field `key`. -/
    | union (key : String) (vs : Variants)
    | array (τ : Ty)
    /-- `Map<string, τ>`. -/
    | map (τ : Ty)
    deriving Repr, BEq, Inhabited

  inductive Fields where
    | nil
    | cons (name : String) (τ : Ty) (rest : Fields)
    deriving Repr, BEq, Inhabited

  inductive Variants where
    | one (t : TagLit) (fs : Fields)
    | cons (t : TagLit) (fs : Fields) (rest : Variants)
    deriving Repr, BEq, Inhabited
end

mutual
  @[reducible] def Ty.denote : Ty → Type
    | .bool => Bool
    | .int => Int
    | .number => Int
    | .string => JSString
    | .tag _ => Unit
    | .lits _ rest => Fin (rest.length + 1)
    | .option _ τ => Option τ.denote
    | .record fs => fs.denote
    | .union _ vs => vs.denote
    | .array τ => List τ.denote
    | .map τ => List (JSString × τ.denote)

  @[reducible] def Fields.denote : Fields → Type
    | .nil => Unit
    | .cons _ τ rest => τ.denote × rest.denote

  @[reducible] def Variants.denote : Variants → Type
    | .one _ fs => fs.denote
    | .cons _ fs rest => fs.denote ⊕ rest.denote
end

mutual
  def Ty.default : (τ : Ty) → τ.denote
    | .bool => false
    | .int => 0
    | .number => 0
    | .string => []
    | .tag _ => ()
    | .lits _ _ => 0
    | .option _ _ => none
    | .record fs => fs.default
    | .union _ vs => vs.default
    | .array _ => []
    | .map _ => []

  def Fields.default : (fs : Fields) → fs.denote
    | .nil => ()
    | .cons _ τ rest => (τ.default, rest.default)

  def Variants.default : (vs : Variants) → vs.denote
    | .one _ fs => fs.default
    | .cons _ fs _ => .inl fs.default
end

/-- Two lists related elementwise. -/
inductive Forall2 (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- A property read on a record as JavaScript does it: a missing own property is
`undefined` (for names that are not `Object.prototype` properties). -/
def fieldOf (kvs : List (String × JSValue)) (f : String) : JSValue := (kvs.lookup f).getD .undefined

mutual
  def Ty.Rep : (τ : Ty) → JSValue → τ.denote → Prop
    | .bool, v, b => v = .bool b
    | .int, v, n => v = .bigint n
    | .number, v, n => v = .number n
    | .string, v, s => v = .string s
    | .tag t, v, _ => v = t.value
    | .lits a as, v, i => v = .string ((a :: as)[i])
    | .option n _, v, none => n.admits v
    | .option _ τ, v, some x => τ.Rep v x
    | .record fs, v, x => ∃ kvs, v = .record kvs ∧ (kvs.map Prod.fst).Nodup ∧ fs.Rep kvs x
    | .union key vs, v, x => ∃ kvs, v = .record kvs ∧ (kvs.map Prod.fst).Nodup ∧ vs.Rep key kvs x
    | .array τ, v, xs => ∃ vs, v = .array vs ∧ Forall2 (fun w x => τ.Rep w x) vs xs
    | .map τ, v, m => ∃ kvs, v = .map kvs ∧ Forall2 (fun p q => p.1 = q.1 ∧ τ.Rep p.2 q.2) kvs m

  def Fields.Rep : (fs : Fields) → List (String × JSValue) → fs.denote → Prop
    | .nil, _, _ => True
    | .cons f τ rest, kvs, (x, xs) => τ.Rep (fieldOf kvs f) x ∧ rest.Rep kvs xs

  def Variants.Rep (key : String) : (vs : Variants) → List (String × JSValue) → vs.denote → Prop
    | .one t fs, kvs, x => fieldOf kvs key = t.value ∧ fs.Rep kvs x
    | .cons t fs _, kvs, .inl x => fieldOf kvs key = t.value ∧ fs.Rep kvs x
    | .cons _ _ rest, kvs, .inr y => rest.Rep key kvs y
end

/-- A safe integer: the range in which the model's numbers are exact. Stated on
`natAbs` with `Nat.ble` so that the kernel, should it unfold it on a partly
symbolic argument, stops after a few steps instead of recursing on the bound. -/
def inRange (n : Int) : Bool := Nat.ble n.natAbs 9007199254740991

/-! ## Primitive types -/

/-- The strings are distinct. -/
def distinctStrs : List JSString → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinctStrs xs

/-- Types whose values `===` compares by value (for a literal union, by index:
its literals must be distinct). -/
def Ty.prim : Ty → Bool
  | .bool | .int | .number | .string | .tag _ => true
  | .lits a as => distinctStrs (a :: as)
  | _ => false

/-- Types with no nullish value, so `x == null` tells an optional's `none` apart. -/
def Ty.nonNullish : Ty → Bool
  | .option _ _ => false
  | _ => true

/-- `===` on denoted primitives. -/
def Ty.beq : (τ : Ty) → τ.denote → τ.denote → Bool
  | .bool, a, b => a == b
  | .int, a, b => a == b
  | .number, a, b => a == b
  | .string, a, b => a == b
  | .tag _, _, _ => true
  | .lits _ _, i, j => i == j
  | _, _, _ => false

/-! ## Fields and variants -/

/-- The position of field `f` of type `τ` in a field list. -/
inductive FIdx : Fields → String → Ty → Type where
  | here : FIdx (.cons f τ rest) f τ
  | there : FIdx rest f τ → FIdx (.cons g σ rest) f τ

def FIdx.get : {fs : Fields} → FIdx fs f τ → fs.denote → τ.denote
  | .cons .., .here, (x, _) => x
  | .cons .., .there i, (_, xs) => i.get xs

def FIdx.set : {fs : Fields} → FIdx fs f τ → fs.denote → τ.denote → fs.denote
  | .cons .., .here, (_, xs), y => (y, xs)
  | .cons .., .there i, (x, xs), y => (x, i.set xs y)

def Fields.names : Fields → List String
  | .nil => []
  | .cons f _ rest => f :: rest.names

/-- The record type of a union's variant: its tag field, then its fields. -/
def vrec (key : String) (t : TagLit) (fs : Fields) : Ty := .record (.cons key (.tag t) fs)

/-- The position of the variant tagged `t` with fields `fs` in a union. -/
inductive VIdx : Variants → TagLit → Fields → Type where
  | one : VIdx (.one t fs) t fs
  | head : VIdx (.cons t fs rest) t fs
  | there : VIdx rest t fs → VIdx (.cons t' fs' rest) t fs

def VIdx.inj : VIdx vs t fs → fs.denote → vs.denote
  | .one, x => x
  | .head, x => .inl x
  | .there i, x => .inr (i.inj x)

/-- The variant's fields, if the union value is that variant. -/
def VIdx.proj : VIdx vs t fs → vs.denote → Option fs.denote
  | .one, y => some y
  | .head, .inl y => some y
  | .head, .inr _ => none
  | .there _, .inl _ => none
  | .there i, .inr w => i.proj w

/-- Case analysis of a union value: the handler gets the variant and its fields.
The match on the value is separate from the recursion on `vs`, so that on a symbolic
value it reduces to a plain `match` (as readable definitions print it). -/
def Variants.elim {R : Type} : (vs : Variants) → vs.denote → (∀ {t fs}, VIdx vs t fs → fs.denote → R) → R
  | .one _ _, y, h => h .one y
  | .cons _ _ rest, u, h => match u with
    | .inl y => h .head y
    | .inr w => rest.elim w fun i y => h (.there i) y

/-- A narrowed type `σ` of a type `τ`: the type a test (`x == null`, a `switch`
on a union's tag) establishes, with its embedding back into `τ`. -/
inductive Narrowing : Ty → Ty → Type where
  /-- `x != null` narrows an optional to its value type. -/
  | some (n : Nullish) (τ : Ty) : Narrowing τ (.option n τ)
  /-- A `case` narrows a union to one of its variants. -/
  | variant (i : VIdx vs t fs) : Narrowing (vrec key t fs) (.union key vs)

def Narrowing.embed : Narrowing σ τ → σ.denote → τ.denote
  | .some _ _, y => Option.some y
  | .variant i, ((), y) => i.inj y

end Ariadne

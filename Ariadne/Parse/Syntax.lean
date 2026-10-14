import Ariadne.Parse.Source

namespace Ariadne.Parse

inductive Ty where
  | number | int53 | bigint | boolean | string | undefined | null | void
  | stringLiteral (units : List UInt16)
  | readonly (ty : Ty)
  | fieldReadonly (ty : Ty)
  | set (element : Ty)
  | iterator (element : Ty)
  | class_ (name : String)
  | array (element : Ty)
  | map (key value : Ty)
  | tuple (elements : List Ty)
  | record (fields : List (String × Ty))
  | union (left right : Ty)
  | named (name : String)
  | function (params : List Ty) (result : Ty)
  deriving Repr, Inhabited

/-- Total type equality. The default derived equality for nested inductives is
opaque to kernel reduction, so the frontend uses this bounded structural walk. -/
def Ty.equalFuel : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .number, .number | .int53, .int53 | .bigint, .bigint | .boolean, .boolean
    | .string, .string | .undefined, .undefined | .null, .null | .void, .void => true
    | .array a, .array b | .readonly a, .readonly b | .fieldReadonly a, .fieldReadonly b | .set a, .set b | .iterator a, .iterator b => equalFuel n a b
    | .stringLiteral a, .stringLiteral b => a == b
    | .class_ a, .class_ b => a == b
    | .map a b, .map c d | .union a b, .union c d => equalFuel n a c && equalFuel n b d
    | .named a, .named b => a == b
    | .tuple a, .tuple b => a.length == b.length && (a.zip b).all (fun (x, y) => equalFuel n x y)
    | .record a, .record b => a.length == b.length && (a.zip b).all
        (fun ((k, x), (l, y)) => k == l && equalFuel n x y)
    | .function a r, .function b s => equalFuel n r s && a.length == b.length &&
        (a.zip b).all (fun (x, y) => equalFuel n x y)
    | _, _ => false

def Ty.depth : Ty → Nat
  | .array a | .readonly a | .fieldReadonly a | .set a | .iterator a => a.depth + 1
  | .map a b | .union a b => max a.depth b.depth + 1
  | .tuple ts => (ts.map Ty.depth).foldl max 0 + 1
  | .record fs => (fs.map (fun p => p.2.depth)).foldl max 0 + 1
  | .function ps r => max ((ps.map Ty.depth).foldl max 0) r.depth + 1
  | _ => 1
termination_by t => sizeOf t
decreasing_by
  all_goals first | decreasing_tactic | skip
  have h := List.sizeOf_lt_of_mem ‹p ∈ fs›
  cases p
  simp only [Prod.mk.sizeOf_spec, Ty.record.sizeOf_spec] at h ⊢
  omega

instance : BEq Ty := ⟨fun a b => Ty.equalFuel (a.depth + b.depth) a b⟩

structure Param where
  name : String
  ty : Ty
  optional : Bool := false
  span : Span := {}
  deriving Repr, BEq, Inhabited

inductive Literal where
  | number (mantissa : Nat) (exponent : Int)
  | bigint (value : Int)
  | string (units : List UInt16)
  | boolean (value : Bool)
  | undefined | null
  deriving Repr, BEq, Inhabited

mutual
  inductive Expr where
    | literal (value : Literal) (span : Span)
    | var (name : String) (span : Span)
    | unary (op : String) (arg : Expr) (span : Span)
    | binary (op : String) (left right : Expr) (span : Span)
    | conditional (condition yes no : Expr) (span : Span)
    | call (callee : Expr) (args : List Expr) (span : Span)
    | member (object : Expr) (field : String) (span : Span)
    | index (object index : Expr) (span : Span)
    | array (elements : List Expr) (span : Span)
    | record (fields : List (String × Expr)) (span : Span)
    | lambda (params : List Param) (body : Stmt) (span : Span)
    | newMap (key value : Ty) (span : Span)
    | newSet (element : Ty) (span : Span)
    | newClass (name : String) (args : List Expr) (span : Span)
    | spread (value : Expr) (span : Span)
    deriving Repr, BEq, Inhabited

  inductive Stmt where
    | block (statements : List Stmt) (span : Span)
    | let_ (mutable : Bool) (name : String) (annotation : Option Ty)
        (value : Expr) (span : Span)
    | assign (target : Expr) (value : Expr) (span : Span)
    /-- Compound updates retain the reference, read it, evaluate the RHS, and
    write it once. The parser keeps local-variable updates as assignments. -/
    | update (target : Expr) (op : String) (value : Expr) (span : Span)
    | expr (value : Expr) (span : Span)
    | if_ (condition : Expr) (yes no : Stmt) (span : Span)
    | while_ (condition : Expr) (body : Stmt) (span : Span)
    | for_ (init : Stmt) (condition : Expr) (update body : Stmt) (span : Span)
    | forOf (mutable : Bool) (name : String) (collection : Expr) (body : Stmt) (span : Span)
    /-- `for (const [first, second] of collection)`. -/
    | forOfPair (mutable : Bool) (first second : String) (collection : Expr) (body : Stmt) (span : Span)
    | measured (measure : Expr) (body : Stmt) (span : Span)
    | switch_ (value : Expr) (cases : List (Option Expr × List Stmt)) (span : Span)
    | return_ (value : Expr) (span : Span)
    | break_ (span : Span)
    | continue_ (span : Span)
    /-- `throw new Error(message)` with a string literal message. -/
    | throw_ (message : List UInt16) (span : Span)
    deriving Repr, BEq, Inhabited
end

def Expr.span : Expr → Span
  | .literal _ s | .var _ s | .unary _ _ s | .binary _ _ _ s
  | .conditional _ _ _ s | .call _ _ s | .member _ _ s | .index _ _ s
  | .array _ s | .record _ s | .lambda _ _ s | .newMap _ _ s
  | .newSet _ s | .newClass _ _ s | .spread _ s => s

def Stmt.span : Stmt → Span
  | .block _ s | .let_ _ _ _ _ s | .assign _ _ s | .update _ _ _ s | .expr _ s
  | .if_ _ _ _ s | .while_ _ _ s | .for_ _ _ _ _ s | .return_ _ s
  | .break_ s | .continue_ s | .forOf _ _ _ _ s | .forOfPair _ _ _ _ _ s | .switch_ _ _ s | .measured _ _ s | .throw_ _ s => s

structure Function where
  name : String
  params : List Param
  result : Ty
  body : Stmt
  exported : Bool := false
  decreases : Option Expr := none
  span : Span := {}
  deriving Repr, BEq, Inhabited

structure Field where
  name : String
  ty : Option Ty
  value : Expr
  private_ : Bool := false
  readonly_ : Bool := false
  span : Span := {}
  deriving Repr, BEq, Inhabited

structure Class where
  name : String
  fields : List Field
  methods : List Function
  constructor_ : Option Function := none
  span : Span := {}
  deriving Repr, BEq, Inhabited

structure Program where
  functions : List Function
  aliases : List (String × Ty) := []
  classes : List Class := []
  deriving Repr, BEq, Inhabited

end Ariadne.Parse

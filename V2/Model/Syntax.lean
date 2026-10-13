/-!
# Source syntax of the subset (trusted)

The untyped, JavaScript-shaped syntax the model evaluates: what the parser produces
once spans and type annotations are stripped. Type annotations have no runtime
meaning in TypeScript, so dropping them loses nothing the evaluator could observe.
Unbraced and braced statement bodies both become statement lists.
-/

namespace V2

/-- Strings are sequences of UTF-16 code units, as in JavaScript. -/
abbrev JSString := List UInt16

/-- A string of Basic Multilingual Plane characters (no surrogates) as UTF-16:
one code unit per character. Printed programs use it for readable literals. -/
def js (s : String) : JSString := s.toList.map fun c => c.toNat.toUInt16

inductive Lit where
  | bool (b : Bool)
  | bigint (n : Int)
  | string (s : JSString)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive UnOp where
  /-- `!e` -/
  | not
  /-- `-e` -/
  | neg
  deriving Repr, BEq, DecidableEq, Inhabited

inductive BinOp where
  | add | sub | mul
  /-- `===` -/
  | eq
  /-- `!==` -/
  | ne
  | lt | le | gt | ge
  /-- `&&`, short-circuiting -/
  | and
  /-- `||`, short-circuiting -/
  | or
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Expr where
  | lit (l : Lit)
  | var (x : String)
  | unary (op : UnOp) (e : Expr)
  | binary (op : BinOp) (a b : Expr)
  /-- `c ? a : b` -/
  | cond (c a b : Expr)
  /-- A call to a function declared in the program. -/
  | call (f : String) (args : List Expr)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  /-- `const x = e;` -/
  | const (x : String) (e : Expr)
  /-- `return e;` -/
  | ret (e : Expr)
  /-- `if (c) { yes } else { no }`; a missing `else` is an empty list. -/
  | ite (c : Expr) (yes no : List Stmt)
  deriving Repr, BEq, Inhabited

/-- Names a statement adds to the scope of the rest of its list. -/
def Stmt.declares : Stmt → List String
  | .const x _ => [x]
  | _ => []

structure Function where
  name : String
  params : List String
  body : List Stmt
  deriving Repr, BEq, Inhabited

/-- Functions in source order. -/
abbrev Program := List Function

end V2

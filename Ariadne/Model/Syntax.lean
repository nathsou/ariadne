/-!
# The model's syntax

The abstract syntax of the TypeScript subset, after type erasure: exactly what the
trusted evaluator runs and what generated theorems are about.
-/

namespace Ariadne

/-- Strings are sequences of UTF-16 code units, as in JavaScript. -/
abbrev JSString := List UInt16

/-- A string of Basic Multilingual Plane characters (no surrogates) as UTF-16:
one code unit per character. Printed programs use it for readable literals. -/
def js (s : String) : JSString := s.toList.map fun c => c.toNat.toUInt16

inductive Lit where
  | undefined
  | null
  | bool (b : Bool)
  /-- An integer-valued `number` literal. -/
  | number (n : Int)
  | bigint (n : Int)
  | string (s : JSString)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive UnOp where
  | not | neg
  /-- What `x++` and `x--` add to `x`: one, in its own numeric type. -/
  | inc | dec
  deriving Repr, BEq, DecidableEq, Inhabited

inductive BinOp where
  | add | sub | mul
  /-- `/` and `%`. -/
  | div | mod
  /-- `Math.floor(a / b)`. -/
  | floorDiv
  /-- `===` and `!==`. -/
  | eq | ne
  | lt | le | gt | ge
  /-- `&&`, `||` and `??` (short-circuiting). -/
  | and | or | coalesce
  /-- `==` and `!=`, supported only with a `null` or `undefined` operand. -/
  | looseEq | looseNe
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Expr where
  | lit (l : Lit)
  | var (x : String)
  | unary (op : UnOp) (e : Expr)
  | binary (op : BinOp) (a b : Expr)
  | cond (c a b : Expr)
  /-- A call of a declared function, or of a local holding a function value. -/
  | call (f : String) (args : List Expr)
  /-- An object literal: `(some name, e)` is `name: e`, `(none, e)` is `...e`. -/
  | record (entries : List (Option String × Expr))
  /-- `e.name`: a record field, or `length` of an array or string. -/
  | field (e : Expr) (name : String)
  /-- An array literal: `(true, e)` is `...e`. -/
  | array (elems : List (Bool × Expr))
  /-- `e[i]`. -/
  | index (e i : Expr)
  /-- `e.name(args)`: an array method. -/
  | method (e : Expr) (name : String) (args : List Expr)
  /-- `(params) => body`. -/
  | arrow (params : List String) (body : Expr)
  /-- `new Map()`. -/
  | newMap
  /-- `this.f.get(k)`, `this.f.has(k)` and `this.f.size` on a `Map` field of the
  object a method runs on. -/
  | stateGet (f : String) (k : Expr)
  | stateHas (f : String) (k : Expr)
  | stateSize (f : String)
  /-- `this.f.keys()` and `this.f.values()`: iterators, accepted only as `...e` in
  an array literal (`Expr.scoped`), where the model evaluates them to arrays. -/
  | stateKeys (f : String)
  | stateValues (f : String)
  /-- `this.m(args)` in an expression: only of a method that changes no state
  (`Expr.scoped`). -/
  | callThis (m : String) (args : List Expr)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | const (x : String) (e : Expr)
  | let_ (x : String) (e : Expr)
  | assign (x : String) (e : Expr)
  | ret (e : Expr)
  | ite (c : Expr) (yes no : List Stmt)
  /-- `{ ss }`: a block scope. -/
  | block (ss : List Stmt)
  /-- `switch (e) { case t: … default: … }`; `none` labels `default`. -/
  | switch (e : Expr) (cases : List (Option Expr × List Stmt))
  | brk
  | cont
  /-- `for (const x of e) { body }`. -/
  | forOf (x : String) (e : Expr) (body : List Stmt)
  /-- `for (const [i, x] of e.entries()) { body }`. -/
  | forEntries (i x : String) (e : Expr) (body : List Stmt)
  /-- `for (let i = 0; i < n; i++) { body }` where `n` is a constant holding a number
  and `body` does not assign `i` (`stmtScoped`): one iteration per `i` in `0 … n-1`. -/
  | forRange (i n : String) (body : List Stmt)
  /-- `while (c) { body }`. -/
  | while_ (c : Expr) (body : List Stmt)
  /-- `this.f.set(k, v);` and `this.f.delete(k);` on a `Map` field. -/
  | stateSet (f : String) (k v : Expr)
  | stateDelete (f : String) (k : Expr)
  /-- `this.m(args);`: a method call that may change the state. -/
  | callThis (m : String) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-- Names a statement adds to the scope of the rest of its list. -/
def Stmt.declares : Stmt → List String
  | .const x _ | .let_ x _ => [x]
  | _ => []

structure Function where
  name : String
  params : List String
  body : List Stmt
  /-- A method of the program's class: its first parameter is `this`, bound to the
  object's state (a record of its fields). -/
  method : Bool := false
  deriving Repr, BEq, Inhabited

/-- Functions in source order. -/
abbrev Program := List Function

end Ariadne

import Ariadne.Model.Syntax

/-!
# The trusted model: a value semantics of the subset

A big-step evaluator over plain JavaScript values, with no heap. Nothing in the
subset mutates an object in place or compares objects by identity (the model
faults on `===` between objects), so JavaScript's reference semantics and this
value semantics agree.

Evaluation is bounded by fuel. Every recursive call consumes fuel (nesting depth,
statements, loop iterations and callback applications), and every definition is
structurally recursive on it, so the evaluator runs compiled (for differential
tests) and reduces in the kernel.

**Claim.** Whenever `run` returns `.ok v`, running the program in JavaScript returns
a value with the same observation as `v` (see `scripts/differential.mjs`). The
model faults wherever the subset leaves JavaScript's behaviour unmodelled:
coercions between types, identity comparisons, prototype properties, numbers
outside the safe-integer range, inconsistent comparators. Faults make no claim.

**Numbers** are integers in ±(2^53 − 1), where binary64 arithmetic is exact. Every
operation producing a number faults outside that range. Negative zero, which
`0 * -1` produces in JavaScript, is not distinguished from zero: in the subset
(no division, `Object.is`, or number formatting beyond integers) the two cannot
be told apart.
-/

namespace Ariadne

inductive JSValue where
  | undefined
  | null
  | bool (b : Bool)
  | number (n : Int)
  | bigint (n : Int)
  | string (s : JSString)
  /-- An object with its own properties in insertion order. -/
  | record (fields : List (String × JSValue))
  | array (elems : List JSValue)
  /-- An arrow function with its captured environment. -/
  | closure (params : List String) (body : Expr) (env : List (String × JSValue))
  /-- A declared function used as a value. -/
  | function (name : String)
  /-- A `Map` with string keys, in insertion order. Maps are only held in the fields
  of the object a method runs on (`this`), which the subset never hands out, so a
  map is never shared and changing it in place equals replacing it. -/
  | map (kvs : List (JSString × JSValue))
  deriving Repr, Inhabited

inductive Fault where
  | timeout
  | typeError (message : String)
  | referenceError (name : String)
  /-- Behaviour the model does not cover. -/
  | unsupported (message : String)
  deriving Repr, BEq, Inhabited

/-- Bindings in scope, innermost first. Lookup finds the innermost binding. -/
abbrev Env := List (String × JSValue)

inductive Outcome where
  /-- Ran to the end of the list; the environment includes its declarations. -/
  | normal (env : Env)
  /-- A `return`, with the environment it ran in (a method's state is read from it). -/
  | returned (value : JSValue) (env : Env)
  | broke (env : Env)
  | continued (env : Env)
  deriving Repr, Inhabited

/-! ## Primitive operations -/

def maxSafe : Int := 2 ^ 53 - 1

/-- A number result, if it is a safe integer. -/
def number (n : Int) : Except Fault JSValue :=
  if -maxSafe ≤ n ∧ n ≤ maxSafe then .ok (.number n) else .error (.unsupported "number outside the safe range")

/-- `a < b` on strings: lexicographic order of UTF-16 code units. -/
def strLt : JSString → JSString → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else strLt as bs

def strLe (a b : JSString) : Bool := !strLt b a

def Lit.value : Lit → JSValue
  | .undefined => .undefined
  | .null => .null
  | .bool b => .bool b
  | .number n => .number n
  | .bigint n => .bigint n
  | .string s => .string s

def JSValue.nullish : JSValue → Bool
  | .undefined | .null => true
  | _ => false

def unary : UnOp → JSValue → Except Fault JSValue
  | .not, .bool b => .ok (.bool !b)
  | .neg, .number n => number (-n)
  | .neg, .bigint n => .ok (.bigint (-n))
  | _, _ => .error (.typeError "unary operand")

/-- Strict equality of primitives of one type. Objects compare by identity in
JavaScript, which a value semantics cannot model, so they fault. -/
def strictEq : JSValue → JSValue → Except Fault Bool
  | .undefined, .undefined => .ok true
  | .null, .null => .ok true
  | .bool a, .bool b => .ok (a == b)
  | .number a, .number b => .ok (a == b)
  | .bigint a, .bigint b => .ok (a == b)
  | .string a, .string b => .ok (a == b)
  | _, _ => .error (.unsupported "strict equality operands")

/-- Non-short-circuiting binary operators. -/
def binary : BinOp → JSValue → JSValue → Except Fault JSValue
  | .add, .number a, .number b => number (a + b)
  | .add, .bigint a, .bigint b => .ok (.bigint (a + b))
  | .add, .string a, .string b => .ok (.string (a ++ b))
  | .sub, .number a, .number b => number (a - b)
  | .sub, .bigint a, .bigint b => .ok (.bigint (a - b))
  | .mul, .number a, .number b => number (a * b)
  | .mul, .bigint a, .bigint b => .ok (.bigint (a * b))
  | .eq, a, b => return .bool (← strictEq a b)
  | .ne, a, b => return .bool !(← strictEq a b)
  | .lt, .number a, .number b | .lt, .bigint a, .bigint b => .ok (.bool (decide (a < b)))
  | .le, .number a, .number b | .le, .bigint a, .bigint b => .ok (.bool (decide (a ≤ b)))
  | .gt, .number a, .number b | .gt, .bigint a, .bigint b => .ok (.bool (decide (b < a)))
  | .ge, .number a, .number b | .ge, .bigint a, .bigint b => .ok (.bool (decide (b ≤ a)))
  | .lt, .string a, .string b => .ok (.bool (strLt a b))
  | .le, .string a, .string b => .ok (.bool (strLe a b))
  | .gt, .string a, .string b => .ok (.bool (strLt b a))
  | .ge, .string a, .string b => .ok (.bool (strLe b a))
  -- `==` with a nullish operand: true exactly when both are nullish.
  | .looseEq, a, b => if a.nullish || b.nullish then .ok (.bool (a.nullish && b.nullish))
      else .error (.unsupported "== without a nullish operand")
  | .looseNe, a, b => if a.nullish || b.nullish then .ok (.bool !(a.nullish && b.nullish))
      else .error (.unsupported "!= without a nullish operand")
  | _, _, _ => .error (.typeError "binary operands")

/-! ## Objects and arrays -/

/-- Properties every object inherits from `Object.prototype`: reading one that is
not an own property does not give `undefined`, so the model refuses it. -/
def protoNames : List String :=
  ["constructor", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString", "toString",
   "valueOf", "__proto__", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__"]

/-- `e.name`. -/
def getField : JSValue → String → Except Fault JSValue
  | .record kvs, f => match kvs.lookup f with
    | some v => .ok v
    | none => if protoNames.contains f then .error (.unsupported s!"prototype property {f}") else .ok .undefined
  -- JavaScript bounds lengths by 2^32 - 1 (a `RangeError` beyond); like memory and
  -- stack depth, the model treats that as a resource limit and does not model it.
  | .array xs, "length" => .ok (.number xs.length)
  | .string s, "length" => .ok (.number s.length)
  | _, f => .error (.unsupported s!"property {f}")

/-- Defining a property: an existing key keeps its position. -/
def upsert : List (String × JSValue) → String → JSValue → List (String × JSValue)
  | [], f, v => [(f, v)]
  | (k, w) :: rest, f, v => if k == f then (k, v) :: rest else (k, w) :: upsert rest f v

/-- `f: v` in an object literal. The literal syntax `__proto__: v` sets the
prototype instead of defining a property, so the model refuses it. -/
def setField (kvs : List (String × JSValue)) (f : String) (v : JSValue) : Except Fault (List (String × JSValue)) :=
  if f == "__proto__" then .error (.unsupported "__proto__ in an object literal") else .ok (upsert kvs f v)

/-- `...v` in an object literal: defines each own property of `v` in order
(`CopyDataProperties`; an own `__proto__` key is copied like any other). -/
def spreadInto (kvs : List (String × JSValue)) : JSValue → Except Fault (List (String × JSValue))
  | .record src => .ok (src.foldl (fun acc (f, v) => upsert acc f v) kvs)
  | .undefined | .null => .ok kvs
  | _ => .error (.unsupported "object spread of a non-record")

/-- `e[i]`. -/
def index : JSValue → JSValue → Except Fault JSValue
  | .array xs, .number i => .ok (if 0 ≤ i then (xs[i.toNat]?).getD .undefined else .undefined)
  | _, _ => .error (.unsupported "indexing")

/-- `xs.includes(x)` (SameValueZero, which is `===` on the model's primitives). -/
def includes (x : JSValue) : List JSValue → Except Fault Bool
  | [] => .ok false
  | y :: ys => do if ← strictEq y x then return true else includes x ys

/-! ## Maps and the object's state

A method's object is the binding `this`: a record of its fields. The subset reads
and changes its `Map` fields only through the `state*` forms. -/

/-- `m.get(k)`. (The map operations are generic in the values: readable definitions
use them too.) -/
def mapGet {α : Type} (kvs : List (JSString × α)) (k : JSString) : Option α := kvs.lookup k

/-- `m.set(k, v)`: an existing key keeps its position, a new one goes last. -/
def mapPut {α : Type} : List (JSString × α) → JSString → α → List (JSString × α)
  | [], k, v => [(k, v)]
  | (k', w) :: rest, k, v => if k' == k then (k', v) :: rest else (k', w) :: mapPut rest k v

/-- `m.delete(k)` (keys are distinct, since only `mapPut` adds them). -/
def mapDel {α : Type} (kvs : List (JSString × α)) (k : JSString) : List (JSString × α) :=
  kvs.filter (·.1 != k)

/-- The `Map` in field `f` of `this`. -/
def stateMap (env : Env) (f : String) : Except Fault (List (JSString × JSValue)) :=
  match env.lookup "this" with
  | some (.record fs) => match fs.lookup f with
    | some (.map kvs) => .ok kvs
    | _ => .error (.unsupported s!"field {f} is not a map")
  | _ => .error (.referenceError "this")

/-- A map key: a string. -/
def mapKey : JSValue → Except Fault JSString
  | .string s => .ok s
  | _ => .error (.unsupported "a map key that is not a string")

/-! ## Sorting

`toSorted` with a comparator gives the one stable order of a consistent comparator
(ECMA-262 requires a stable sort; any two stable sorts by a consistent comparator
agree). The model checks consistency on the array and faults otherwise, then sorts
by insertion. `signs[i][j]` is the sign of `compare(xs[i], xs[j])`. -/

def sign (c : Int) : Int := if c < 0 then -1 else if 0 < c then 1 else 0

def signAt (signs : List (List Int)) (i j : Nat) : Int := (signs[i]?.bind (·[j]?)).getD 0

/-- The comparator's signs form a total preorder on the array. -/
def consistent (signs : List (List Int)) : Bool :=
  let ix := List.range signs.length
  ix.all fun i => ix.all fun j => signAt signs i j == -signAt signs j i &&
    ix.all fun k => (signAt signs i j > 0 || signAt signs j k > 0 || signAt signs i k ≤ 0) &&
      (signAt signs i j ≥ 0 || signAt signs j k > 0 || signAt signs i k < 0) &&
      (signAt signs i j > 0 || signAt signs j k ≥ 0 || signAt signs i k < 0)

/-- Insert index `i` after every index that does not compare greater. -/
def insertBy (signs : List (List Int)) (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if signAt signs i j < 0 then i :: j :: js else j :: insertBy signs i js

def sortIndices (signs : List (List Int)) (n : Nat) : List Nat :=
  (List.range n).foldl (fun acc i => insertBy signs i acc) []

/-! ## Scoping

JavaScript resolves names lexically: a block's declarations are in scope for the
whole block (reading one before its declaration throws), and a local shadows a
function of the same name. The evaluator resolves variables in the environment
and functions in the program, which agrees with JavaScript exactly when no
declaration reuses a name in scope or a function's name. `run` checks this, and
the other static rules below, first; then reading a name before its declaration
is a `referenceError` in both. -/

def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- What the static check tracks: function names, names in scope, the assignable
ones, and whether `break`/`continue` have a target. Methods are named apart from
functions and locals (JavaScript reaches them only as `this.m`). -/
structure Scope where
  fns : List String
  names : List String
  mutable : List String
  inLoop : Bool := false
  inSwitch : Bool := false
  /-- The class's methods, and those that change no state. -/
  methods : List String := []
  pure : List String := []

def Scope.fresh (s : Scope) (x : String) : Bool := x != "this" && !s.names.contains x && !s.fns.contains x

def Scope.bind (s : Scope) (x : String) (mutable : Bool) : Scope :=
  { s with names := x :: s.names, mutable := if mutable then x :: s.mutable else s.mutable }

mutual
  def Expr.scoped (s : Scope) : Expr → Bool
    | .lit _ | .newMap | .stateSize _ => true
    -- `this` is never a value, so the object's maps are never shared; a method is
    -- called only on `this`.
    | .var x => x != "this" && (s.names.contains x || !s.methods.contains x)
    | .unary _ e | .field e _ | .stateGet _ e | .stateHas _ e => e.scoped s
    | .binary _ a b | .index a b => a.scoped s && b.scoped s
    | .cond c a b => c.scoped s && a.scoped s && b.scoped s
    | .call f args => (s.names.contains f || !s.methods.contains f) && Expr.scopedList s args
    -- A call in an expression cannot pass the state it leaves back.
    | .callThis m args => s.pure.contains m && Expr.scopedList s args
    -- Iterators: only spread into an array literal (`scopedElems`).
    | .stateKeys _ | .stateValues _ => false
    | .method e _ args => e.scoped s && Expr.scopedCallbacks s args
    | .record entries => Expr.scopedEntries s entries
    | .array elems => Expr.scopedElems s elems
    -- A closure holds a snapshot of its environment, which equals JavaScript's
    -- capture by reference only if it is called before any captured binding can be
    -- reassigned: arrows may appear only as array-method arguments, which apply them
    -- at once (`scopedCallbacks`).
    | .arrow _ _ => false

  def Expr.scopedList (s : Scope) : List Expr → Bool
    | [] => true
    | e :: es => e.scoped s && Expr.scopedList s es

  /-- Arguments of an array method: values, or arrow functions applied at once. -/
  def Expr.scopedCallbacks (s : Scope) : List Expr → Bool
    | [] => true
    | .arrow ps body :: es => distinct ps && ps.all s.fresh &&
        body.scoped { s with names := ps ++ s.names } && Expr.scopedCallbacks s es
    | e :: es => e.scoped s && Expr.scopedCallbacks s es

  def Expr.scopedEntries (s : Scope) : List (Option String × Expr) → Bool
    | [] => true
    | (_, e) :: es => e.scoped s && Expr.scopedEntries s es

  def Expr.scopedElems (s : Scope) : List (Bool × Expr) → Bool
    | [] => true
    | (true, .stateKeys _) :: es | (true, .stateValues _) :: es => Expr.scopedElems s es
    | (_, e) :: es => e.scoped s && Expr.scopedElems s es
end

/-- The scope after a statement list's declarations. -/
def Scope.after (s : Scope) (ss : List Stmt) : Scope :=
  ss.foldl (fun s st => st.declares.foldl (·.bind · (st matches .let_ ..)) s) s

mutual
  /-- The statements, run in scope `s`, declare no name in scope and no function
  name, assign only `let` bindings and parameters, and `break`/`continue` only
  inside a loop or `switch`. -/
  def stmtsScoped (s : Scope) : List Stmt → Bool
    | [] => true
    | st :: rest => stmtScoped s st && stmtsScoped (st.declares.foldl (·.bind · (st matches .let_ ..)) s) rest

  def stmtScoped (s : Scope) : Stmt → Bool
    | .const x e | .let_ x e => s.fresh x && e.scoped s
    | .assign x e => s.mutable.contains x && e.scoped s
    | .ret e => e.scoped s
    | .ite c yes no => c.scoped s && stmtsScoped s yes && stmtsScoped s no
    | .block ss => stmtsScoped s ss
    | .switch e cases => e.scoped s && casesScoped { s with inSwitch := true } cases
    | .brk => s.inLoop || s.inSwitch
    | .cont => s.inLoop
    | .forOf x e body => s.fresh x && e.scoped s && stmtsScoped { s.bind x false with inLoop := true } body
    | .forEntries i x e body => i != x && s.fresh i && s.fresh x && e.scoped s &&
        stmtsScoped { (s.bind i false).bind x false with inLoop := true } body
    | .forRange i n body => s.fresh i && s.names.contains n && !s.mutable.contains n &&
        stmtsScoped { s.bind i false with inLoop := true } body
    | .stateSet _ k v => k.scoped s && v.scoped s
    | .stateDelete _ k => k.scoped s
    | .callThis m args => s.methods.contains m && Expr.scopedList s args

  /-- A `switch` body is one block: declarations in one case are in scope (and in
  their temporal dead zone) in the following ones. -/
  def casesScoped (s : Scope) : List (Option Expr × List Stmt) → Bool
    | [] => true
    | (label, body) :: rest =>
      (match label with | some t => t.scoped s | none => true) && stmtsScoped s body &&
        casesScoped (s.after body) rest
end

mutual
  /-- The statements change the object's state (directly or by a method call). -/
  def stmtsMutate : List Stmt → Bool
    | [] => false
    | st :: rest => stmtMutates st || stmtsMutate rest

  def stmtMutates : Stmt → Bool
    | .stateSet .. | .stateDelete .. | .callThis .. => true
    | .ite _ yes no => stmtsMutate yes || stmtsMutate no
    | .block ss | .forOf _ _ ss | .forEntries _ _ _ ss | .forRange _ _ ss => stmtsMutate ss
    | .switch _ cases => casesMutate cases
    | _ => false

  def casesMutate : List (Option Expr × List Stmt) → Bool
    | [] => false
    | (_, body) :: rest => stmtsMutate body || casesMutate rest
end

/- No statement binds or assigns `this` (implied by the scoping rules; checked
directly so that the store model's agreement needs no further argument). -/

mutual
  def stmtsThisFree : List Stmt → Bool
    | [] => true
    | s :: rest => stmtThisFree s && stmtsThisFree rest

  def stmtThisFree : Stmt → Bool
    | .const x _ | .let_ x _ | .assign x _ => x != "this"
    | .ite _ yes no => stmtsThisFree yes && stmtsThisFree no
    | .block ss => stmtsThisFree ss
    | .switch _ cases => casesThisFree cases
    | .forOf x _ body => x != "this" && stmtsThisFree body
    | .forEntries i x _ body => i != "this" && x != "this" && stmtsThisFree body
    | .forRange i _ body => i != "this" && stmtsThisFree body
    | .ret _ | .brk | .cont | .stateSet .. | .stateDelete .. | .callThis .. => true

  def casesThisFree : List (Option Expr × List Stmt) → Bool
    | [] => true
    | (_, body) :: rest => stmtsThisFree body && casesThisFree rest
end

/-- A method's first parameter is `this`; other functions have no `this`. -/
def Function.thisOk (fn : Function) : Bool :=
  if fn.method then fn.params.head? == some "this" else !fn.params.contains "this"

def Program.scoped (p : Program) : Bool :=
  let fns := (p.filter (!·.method)).map (·.name)
  let methods := (p.filter (·.method)).map (·.name)
  let pure := (p.filter fun fn => fn.method && !stmtsMutate fn.body).map (·.name)
  distinct (p.map (·.name)) && p.all fun fn =>
    distinct fn.params && fn.params.all (!fns.contains ·) && fn.thisOk && stmtsThisFree fn.body &&
      stmtsScoped { fns, names := fn.params, mutable := fn.params.filter (· != "this"), methods, pure } fn.body

/-! ## Evaluation -/

/-- Leaving a block discards its declarations: keep the bindings that were in scope
when it started (declarations are added at the front; assignment keeps positions). -/
def restore (outer inner : Env) : Env := inner.drop (inner.length - outer.length)

/-- Assign the innermost binding of `x`. -/
def assign (x : String) (v : JSValue) : Env → Except Fault Env
  | [] => .error (.referenceError x)
  | (y, w) :: env => if y == x then .ok ((y, v) :: env) else return (y, w) :: (← assign x v env)

/-- Replace the `Map` in field `f` of `this`. -/
def setStateMap (env : Env) (f : String) (kvs : List (JSString × JSValue)) : Except Fault Env :=
  match env.lookup "this" with
  | some (.record fs) => assign "this" (.record (upsert fs f (.map kvs))) env
  | _ => .error (.referenceError "this")

/-- The object's state at the end of a method. -/
def thisOf (env : Env) : Except Fault JSValue :=
  match env.lookup "this" with
  | some t => .ok t
  | none => .error (.referenceError "this")

/-- Parameters bound to arguments: missing arguments are `undefined`, extra ones are
ignored, as in JavaScript. -/
def bindParams : List String → List JSValue → Env
  | [], _ => []
  | x :: xs, [] => (x, .undefined) :: bindParams xs []
  | x :: xs, v :: vs => (x, v) :: bindParams xs vs

/-- The iterations of `for (const [i, x] of xs.entries())`: each element with its index. -/
def entryBindings (i x : String) (xs : List JSValue) : List Env :=
  xs.zipIdx.map fun p => [(x, p.1), (i, .number p.2)]

/-- The iterations of `for (let i = 0; i < m; i++)`. -/
def rangeBindings (i : String) (m : Int) : List Env :=
  (List.range m.toNat).map fun (j : Nat) => [(i, JSValue.number (Int.ofNat j))]

/-- Leaving a block: discard its declarations, and turn `break`/`continue` aimed at
an enclosing construct back into outcomes in the outer environment. -/
def Outcome.restore (outer : Env) : Outcome → Outcome
  | .normal env => .normal (Ariadne.restore outer env)
  | .returned v env => .returned v env
  | .broke env => .broke (Ariadne.restore outer env)
  | .continued env => .continued (Ariadne.restore outer env)

mutual
  def evalExpr (p : Program) : Nat → Env → Expr → Except Fault JSValue
    | 0, _, _ => .error .timeout
    | _ + 1, _, .lit l => .ok l.value
    | _ + 1, env, .var x => match env.lookup x with
      | some v => .ok v
      | none => if p.any (·.name == x) then .ok (.function x) else .error (.referenceError x)
    | n + 1, env, .unary op e => do unary op (← evalExpr p n env e)
    | n + 1, env, .binary .and a b => do
      match ← evalExpr p n env a with
      | .bool false => .ok (.bool false)
      | .bool true => evalExpr p n env b
      | _ => .error (.unsupported "&& operand")
    | n + 1, env, .binary .or a b => do
      match ← evalExpr p n env a with
      | .bool true => .ok (.bool true)
      | .bool false => evalExpr p n env b
      | _ => .error (.unsupported "|| operand")
    | n + 1, env, .binary .coalesce a b => do
      let v ← evalExpr p n env a
      if v.nullish then evalExpr p n env b else .ok v
    | n + 1, env, .binary op a b => do
      let x ← evalExpr p n env a
      let y ← evalExpr p n env b
      binary op x y
    | n + 1, env, .cond c a b => do
      match ← evalExpr p n env c with
      | .bool true => evalExpr p n env a
      | .bool false => evalExpr p n env b
      | _ => .error (.unsupported "condition")
    | n + 1, env, .call f args => do
      let vs ← evalArgs p n env args
      match env.lookup f with
      | some v => apply p n v vs
      | none => call p n f vs
    | n + 1, env, .record entries => evalEntries p n env [] entries
    | n + 1, env, .field e f => do getField (← evalExpr p n env e) f
    | n + 1, env, .array elems => return .array (← evalElems p n env elems)
    | n + 1, env, .index e i => do index (← evalExpr p n env e) (← evalExpr p n env i)
    | n + 1, env, .method e m args => do
      let recv ← evalExpr p n env e
      let vs ← evalArgs p n env args
      match recv, m, vs with
      | .array xs, "includes", [x] => return .bool (← includes x xs)
      | .array xs, "some", [f] => return .bool (← someApply p n f xs 0 recv)
      | .array xs, "every", [f] => return .bool (← everyApply p n f xs 0 recv)
      | .array xs, "find", [f] => findApply p n f xs 0 recv
      | .array xs, "filter", [f] => return .array (← filterApply p n f xs 0 recv)
      | .array xs, "map", [f] => return .array (← mapApply p n f xs 0 recv)
      | .array xs, "toSorted", [f] => do
        let signs ← compareAll p n f xs xs
        if consistent signs then return .array ((sortIndices signs xs.length).filterMap (xs[·]?))
        else .error (.unsupported "inconsistent comparator")
      | _, _, _ => .error (.unsupported s!"method {m}")
    | _ + 1, env, .arrow ps body => .ok (.closure ps body env)
    | _ + 1, _, .newMap => .ok (.map [])
    | n + 1, env, .stateGet f k => do
      let kvs ← stateMap env f
      let key ← mapKey (← evalExpr p n env k)
      return (mapGet kvs key).getD .undefined
    | n + 1, env, .stateHas f k => do
      let kvs ← stateMap env f
      let key ← mapKey (← evalExpr p n env k)
      return .bool (mapGet kvs key).isSome
    | _ + 1, env, .stateSize f => do return .number (← stateMap env f).length
    | _ + 1, env, .stateKeys f => do return .array ((← stateMap env f).map (.string ·.1))
    | _ + 1, env, .stateValues f => do return .array ((← stateMap env f).map (·.2))
    | n + 1, env, .callThis m args => do
      let vs ← evalArgs p n env args
      call p n m ((← thisOf env) :: vs)

  def evalArgs (p : Program) : Nat → Env → List Expr → Except Fault (List JSValue)
    | 0, _, _ => .error .timeout
    | _ + 1, _, [] => .ok []
    | n + 1, env, e :: es => do
      let v ← evalExpr p n env e
      let vs ← evalArgs p n env es
      return v :: vs

  def evalEntries (p : Program) : Nat → Env → List (String × JSValue) → List (Option String × Expr) →
      Except Fault JSValue
    | 0, _, _, _ => .error .timeout
    | _ + 1, _, kvs, [] => .ok (.record kvs)
    | n + 1, env, kvs, (some f, e) :: rest => do
      evalEntries p n env (← setField kvs f (← evalExpr p n env e)) rest
    | n + 1, env, kvs, (none, e) :: rest => do
      evalEntries p n env (← spreadInto kvs (← evalExpr p n env e)) rest

  def evalElems (p : Program) : Nat → Env → List (Bool × Expr) → Except Fault (List JSValue)
    | 0, _, _ => .error .timeout
    | _ + 1, _, [] => .ok []
    | n + 1, env, (false, e) :: rest => do
      let v ← evalExpr p n env e
      return v :: (← evalElems p n env rest)
    | n + 1, env, (true, e) :: rest => do
      match ← evalExpr p n env e with
      | .array xs => return xs ++ (← evalElems p n env rest)
      | _ => .error (.unsupported "array spread of a non-array")

  /-- Call a function value. -/
  def apply (p : Program) : Nat → JSValue → List JSValue → Except Fault JSValue
    | 0, _, _ => .error .timeout
    | n + 1, .closure ps body cenv, vs => evalExpr p n (bindParams ps vs ++ cenv) body
    | n + 1, .function f, vs => call p n f vs
    | _ + 1, _, _ => .error (.typeError "not a function")

  /-- The callback of an array method gets the element, its index and the array. -/
  def someApply (p : Program) : Nat → JSValue → List JSValue → Nat → JSValue → Except Fault Bool
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, [], _, _ => .ok false
    | n + 1, f, x :: xs, i, arr => do
      match ← apply p n f [x, .number i, arr] with
      | .bool true => .ok true
      | .bool false => someApply p n f xs (i + 1) arr
      | _ => .error (.unsupported "callback result")

  def everyApply (p : Program) : Nat → JSValue → List JSValue → Nat → JSValue → Except Fault Bool
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, [], _, _ => .ok true
    | n + 1, f, x :: xs, i, arr => do
      match ← apply p n f [x, .number i, arr] with
      | .bool false => .ok false
      | .bool true => everyApply p n f xs (i + 1) arr
      | _ => .error (.unsupported "callback result")

  def findApply (p : Program) : Nat → JSValue → List JSValue → Nat → JSValue → Except Fault JSValue
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, [], _, _ => .ok .undefined
    | n + 1, f, x :: xs, i, arr => do
      match ← apply p n f [x, .number i, arr] with
      | .bool true => .ok x
      | .bool false => findApply p n f xs (i + 1) arr
      | _ => .error (.unsupported "callback result")

  def filterApply (p : Program) : Nat → JSValue → List JSValue → Nat → JSValue → Except Fault (List JSValue)
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, [], _, _ => .ok []
    | n + 1, f, x :: xs, i, arr => do
      match ← apply p n f [x, .number i, arr] with
      | .bool true => return x :: (← filterApply p n f xs (i + 1) arr)
      | .bool false => filterApply p n f xs (i + 1) arr
      | _ => .error (.unsupported "callback result")

  def mapApply (p : Program) : Nat → JSValue → List JSValue → Nat → JSValue → Except Fault (List JSValue)
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, [], _, _ => .ok []
    | n + 1, f, x :: xs, i, arr => do
      let y ← apply p n f [x, .number i, arr]
      return y :: (← mapApply p n f xs (i + 1) arr)

  /-- Signs of `f(x, y)` for each `x` in `xs` and `y` in `all`. -/
  def compareAll (p : Program) : Nat → JSValue → List JSValue → List JSValue → Except Fault (List (List Int))
    | 0, _, _, _ => .error .timeout
    | _ + 1, _, [], _ => .ok []
    | n + 1, f, x :: xs, all => return (← compareRow p n f x all) :: (← compareAll p n f xs all)

  def compareRow (p : Program) : Nat → JSValue → JSValue → List JSValue → Except Fault (List Int)
    | 0, _, _, _ => .error .timeout
    | _ + 1, _, _, [] => .ok []
    | n + 1, f, x, y :: ys => do
      match ← apply p n f [x, y] with
      | .number c => return sign c :: (← compareRow p n f x ys)
      | _ => .error (.unsupported "comparator result")

  /-- Calls bind the parameters in a fresh environment; falling off the end of the
  body returns `undefined`. -/
  def call (p : Program) : Nat → String → List JSValue → Except Fault JSValue
    | 0, _, _ => .error .timeout
    | n + 1, f, vs => match p.find? (·.name == f) with
      | none => .error (.referenceError f)
      | some fn => do
        match ← execStmts p n (bindParams fn.params vs) fn.body with
        | .returned v _ => .ok v
        | .normal _ => .ok .undefined
        | _ => .error (.unsupported "break or continue outside a loop")

  /-- Call a method: its result and the object's state when it ends. -/
  def callState (p : Program) : Nat → String → List JSValue → Except Fault (JSValue × JSValue)
    | 0, _, _ => .error .timeout
    | n + 1, m, vs => match p.find? (·.name == m) with
      | none => .error (.referenceError m)
      | some fn => if fn.method then do
          match ← execStmts p n (bindParams fn.params vs) fn.body with
          | .returned v env => return (v, ← thisOf env)
          | .normal env => return (.undefined, ← thisOf env)
          | _ => .error (.unsupported "break or continue outside a loop")
        else .error (.unsupported s!"{m} is not a method")

  def execStmts (p : Program) : Nat → Env → List Stmt → Except Fault Outcome
    | 0, _, _ => .error .timeout
    | _ + 1, env, [] => .ok (.normal env)
    | n + 1, env, s :: rest => do
      match ← execStmt p n env s with
      | .normal env' => execStmts p n env' rest
      | o => .ok o

  def execStmt (p : Program) : Nat → Env → Stmt → Except Fault Outcome
    | 0, _, _ => .error .timeout
    | n + 1, env, .const x e | n + 1, env, .let_ x e => do
      let v ← evalExpr p n env e
      return .normal ((x, v) :: env)
    | n + 1, env, .assign x e => do
      let v ← evalExpr p n env e
      return .normal (← assign x v env)
    | n + 1, env, .ret e => do
      return .returned (← evalExpr p n env e) env
    | n + 1, env, .ite c yes no => do
      let branch ← match ← evalExpr p n env c with
        | .bool true => .ok yes
        | .bool false => .ok no
        | _ => .error (.unsupported "condition")
      return (← execStmts p n env branch).restore env
    | n + 1, env, .block ss => return (← execStmts p n env ss).restore env
    | n + 1, env, .switch e cases => do
      let v ← evalExpr p n env e
      match ← findCase p n env v cases 0 with
      | none => .ok (.normal env)
      | some i =>
        match (← execStmts p n env ((cases.drop i).flatMap (·.2))).restore env with
        | .broke env' => .ok (.normal env')
        | o => .ok o
    | _ + 1, env, .brk => .ok (.broke env)
    | _ + 1, env, .cont => .ok (.continued env)
    | n + 1, env, .forOf x e body => do
      match ← evalExpr p n env e with
      | .array xs => loop p n env (xs.map fun v => [(x, v)]) body
      | _ => .error (.unsupported "for-of over a non-array")
    | n + 1, env, .forEntries i x e body => do
      match ← evalExpr p n env e with
      | .array xs => loop p n env (entryBindings i x xs) body
      | _ => .error (.unsupported "entries of a non-array")
    | n + 1, env, .forRange i k body => do
      match env.lookup k with
      -- `loop` with fuel `n` times out before reaching iteration `n`, so iterations
      -- beyond the fuel are not built.
      | some (.number m) => loop p n env (rangeBindings i (min m n)) body
      | some _ => .error (.unsupported "a counted loop's bound that is not a number")
      | none => .error (.referenceError k)
    | n + 1, env, .stateSet f k v => do
      let kvs ← stateMap env f
      let key ← mapKey (← evalExpr p n env k)
      let w ← evalExpr p n env v
      return .normal (← setStateMap env f (mapPut kvs key w))
    | n + 1, env, .stateDelete f k => do
      let kvs ← stateMap env f
      let key ← mapKey (← evalExpr p n env k)
      return .normal (← setStateMap env f (mapDel kvs key))
    | n + 1, env, .callThis m args => do
      let vs ← evalArgs p n env args
      let t ← thisOf env
      let (_, t') ← callState p n m (t :: vs)
      return .normal (← assign "this" t' env)

  /-- One iteration per element: run the body with the iteration's bindings. -/
  def loop (p : Program) : Nat → Env → List Env → List Stmt → Except Fault Outcome
    | 0, _, _, _ => .error .timeout
    | _ + 1, env, [], _ => .ok (.normal env)
    | n + 1, env, bs :: rest, body => do
      match (← execStmts p n (bs ++ env) body).restore env with
      | .returned v env' => .ok (.returned v env')
      | .broke env' => .ok (.normal env')
      | .normal env' | .continued env' => loop p n env' rest body

  /-- The index of the case a `switch` on `v` starts at: the first whose label is
  `===` to `v` (labels are evaluated in order until one matches), else `default`. -/
  def findCase (p : Program) : Nat → Env → JSValue → List (Option Expr × List Stmt) → Nat →
      Except Fault (Option Nat)
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, _, _, [], _ => .ok none
    | n + 1, env, v, (some t, _) :: rest, i => do
      if ← strictEq v (← evalExpr p n env t) then return some i else findCase p n env v rest (i + 1)
    | n + 1, env, v, (none, _) :: rest, i => do
      match ← findCase p n env v rest (i + 1) with
      | some j => return some j
      | none => return some i
end

/-- Call `f` in `p`, refusing programs whose scoping the evaluator does not model. -/
def run (p : Program) (fuel : Nat) (f : String) (args : List JSValue) : Except Fault JSValue :=
  if p.scoped then call p fuel f args else .error (.unsupported "program fails the static scoping check")

/-- Call method `m` on an object whose state is `this`: its result and the state it
leaves. -/
def runMethod (p : Program) (fuel : Nat) (m : String) (this : JSValue) (args : List JSValue) :
    Except Fault (JSValue × JSValue) :=
  if p.scoped then callState p fuel m (this :: args) else .error (.unsupported "program fails the static scoping check")

/-- `f` eventually stabilises at `a`: every budget from some point on gives `a`. -/
def Converges (f : Nat → α) (a : α) : Prop := ∃ n, ∀ m, n ≤ m → f m = a

end Ariadne

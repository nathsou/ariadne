import Ariadne.Syntax
import Init.Data.Float.Model.Float

namespace Ariadne

/-- Strings are UTF-16 code units, including isolated surrogates. -/
abbrev JSString := List UInt16
abbrev Env := List (String × Nat)

instance : Repr Float.Model where
  reprPrec f _ := s!"Float.Model.ofBits {f.toBits.toNat}"

inductive Value where
  | number (value : Float.Model)
  | bigint (value : Int)
  | boolean (value : Bool)
  | string (value : JSString)
  | undefined | null
  | ref (location : Nat)
  | function (name : String)
  | method (location : Nat) (name : String)
  | stringMethod (value : JSString) (name : String)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Object where
  | cell (value : Value)
  | array (values : List Value)
  | record (fields : List (String × Value))
  | map (entries : List (Value × Value))
  | set (values : List Value)
  | iterator (values : List Value)
  | instance_ (name : String) (fields : List (String × Value))
  | closure (params : List Param) (body : Stmt) (captured : Env)
  deriving Repr, BEq, Inhabited

structure State where
  env : Env := []
  heap : List Object := []
  deriving Repr, BEq, Inhabited

inductive Fault where
  | timeout
  | typeError (message : String)
  | rangeError (message : String)
  | referenceError (name : String)
  | invariant (message : String)
  /-- A source `throw new Error(message)`. -/
  | thrown (message : JSString)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Result := Except Fault

def Value.ofLiteral : Literal → Value
  | .number m e => .number (Float.Model.ofScientific m e)
  | .bigint n => .bigint n
  | .boolean b => .boolean b
  | .string s => .string s
  | .undefined => .undefined
  | .null => .null

def Value.truthy : Value → Bool
  | .boolean b => b
  | .number n => !n.isNaN && !(n == Float.Model.ofNat 0)
  | .bigint n => n != 0
  | .string s => !s.isEmpty
  | .undefined | .null => false
  | _ => true

def strictEqual : Value → Value → Bool
  | .number x, .number y => x == y
  | .bigint x, .bigint y => x == y
  | .boolean x, .boolean y => x == y
  | .string x, .string y => x == y
  | .undefined, .undefined | .null, .null => true
  | .ref x, .ref y => x == y
  | _, _ => false

/-- Map equality differs from `===` specifically on NaN. -/
def sameValueZero (a b : Value) : Bool :=
  match a, b with
  | .number x, .number y => (x.isNaN && y.isNaN) || x == y
  | _, _ => strictEqual a b

def canonicalKey : Value → Value
  | .number x => .number (if x == Float.Model.ofNat 0 then Float.Model.ofNat 0 else x)
  | x => x

def mapGet (entries : List (Value × Value)) (key : Value) : Value :=
  ((entries.find? fun p => sameValueZero p.1 key).map Prod.snd).getD .undefined

def mapHas (entries : List (Value × Value)) (key : Value) : Bool :=
  entries.any fun p => sameValueZero p.1 key

/-- Replacement preserves order; new keys are appended. -/
def mapSet : List (Value × Value) → Value → Value → List (Value × Value)
  | [], key, value => [(canonicalKey key, value)]
  | (k, v) :: rest, key, value =>
    if sameValueZero k key then (k, value) :: rest
    else (k, v) :: mapSet rest key value

def mapDelete (entries : List (Value × Value)) (key : Value) : List (Value × Value) :=
  entries.filter fun p => !sameValueZero p.1 key

/-- ECMAScript remainder, computed exactly on the operands' binary significands. -/
def numberRemainder (a b : Float.Model) : Float.Model :=
  match a.unpack, b.unpack with
  | .notANumber, _ | _, .notANumber | .infinity _, _ | _, .zero _ => Float.Model.nan
  | _, .infinity _ | .zero _, _ => a
  | .finite sa ma ea _, .finite _ mb eb _ =>
    let exponent := min ea eb
    let numerator := ma * 2 ^ (ea - exponent).toNat
    let denominator := mb * 2 ^ (eb - exponent).toNat
    Float.Model.pack (Float.Model.UnpackedFloat.round Float.Model.Format.binary64
      sa (numerator % denominator) exponent)

def unary (op : String) (v : Value) : Result Value :=
  match op, v with
  | "#nonNull", v => .ok v -- TypeScript assertion: erased, including at runtime.
  | "!", v => .ok (.boolean (!v.truthy))
  | "-", .bigint n => .ok (.bigint (-n))
  | "-", .number n => .ok (.number (-n))
  | "+", .number n => .ok (.number n)
  | _, _ => .error (.typeError s!"invalid operand for '{op}'")

def binary (op : String) (a b : Value) : Result Value := do
  if op == "==" || op == "!=" then
    let equal := (a == .null || a == .undefined) && (b == .null || b == .undefined)
    return .boolean (if op == "==" then equal else !equal)
  if op == "===" then return .boolean (strictEqual a b)
  if op == "!==" then return .boolean (!strictEqual a b)
  match a, b with
  | .bigint x, .bigint y =>
    match op with
    | "+" => return .bigint (x + y)
    | "-" => return .bigint (x - y)
    | "*" => return .bigint (x * y)
    | "/" => if y == 0 then throw (.rangeError "bigint division by zero") else return .bigint (Int.tdiv x y)
    | "%" => if y == 0 then throw (.rangeError "bigint division by zero") else return .bigint (Int.tmod x y)
    | "<" => return .boolean (x < y) | "<=" => return .boolean (x ≤ y)
    | ">" => return .boolean (x > y) | ">=" => return .boolean (x ≥ y)
    | _ => throw (.typeError s!"invalid bigint operator '{op}'")
  | .number x, .number y =>
    match op with
    | "+" => return .number (x + y) | "-" => return .number (x - y)
    | "*" => return .number (x * y) | "/" => return .number (x / y)
    | "%" => return .number (numberRemainder x y)
    | "<" => return .boolean (x < y) | "<=" => return .boolean (x ≤ y)
    | ">" => return .boolean (x > y) | ">=" => return .boolean (x ≥ y)
    | _ => throw (.typeError s!"invalid number operator '{op}'")
  | .string x, .string y =>
    match op with
    | "+" => return .string (x ++ y)
    | "<" => return .boolean (compare x y == .lt)
    | "<=" => return .boolean (compare x y != .gt)
    | ">" => return .boolean (compare x y == .gt)
    | ">=" => return .boolean (compare x y != .lt)
    | _ => throw (.typeError s!"invalid string operator '{op}'")
  | _, _ => throw (.typeError "mixed operand types require an explicit conversion")

/-- Only nonnegative integral finite numbers can address a dense array element. -/
def indexOf : Value → Option Nat
  | .number n =>
    let i := n.unpack.toInt 0 0
    if n.isFinite && i ≥ 0 && Float.Model.ofInt i == n then some i.toNat else none
  | _ => none

def State.alloc (s : State) (object : Object) : Nat × State :=
  (s.heap.length, { s with heap := s.heap ++ [object] })

def State.lookup (s : State) (name : String) : Result Value := do
  let some (_, loc) := s.env.find? (fun p => p.1 == name)
    | throw (.referenceError name)
  match s.heap[loc]? with
  | some (.cell value) => return value
  | _ => throw (.invariant "variable does not reference a cell")

def State.declare (s : State) (name : String) (value : Value) : State :=
  let (loc, s) := s.alloc (.cell value)
  { s with env := (name, loc) :: s.env }

def State.write (s : State) (loc : Nat) (object : Object) : Result State :=
  if loc < s.heap.length then .ok { s with heap := s.heap.set loc object }
  else .error (.invariant "invalid heap location")

def State.assign (s : State) (name : String) (value : Value) : Result State := do
  let some (_, loc) := s.env.find? (fun p => p.1 == name)
    | throw (.referenceError name)
  s.write loc (.cell value)

end Ariadne

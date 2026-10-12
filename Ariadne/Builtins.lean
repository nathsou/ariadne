import Ariadne.Value

namespace Ariadne.Builtins

/-- Math.trunc preserves negative zero. -/
def numberTrunc (x : Float.Model) : Float.Model :=
  if !x.isFinite || x == Float.Model.ofNat 0 then x else
    let i := x.unpack.toInt 0 0
    if i == 0 && x < Float.Model.ofNat 0 then -(Float.Model.ofNat 0) else Float.Model.ofInt i

/-- Math.floor preserves existing signed zero and rounds toward negative infinity. -/
def numberFloor (x : Float.Model) : Float.Model :=
  if !x.isFinite || x == Float.Model.ofNat 0 then x else
    let i := x.unpack.toInt 0 0
    Float.Model.ofInt (if Float.Model.ofInt i > x then i - 1 else i)

def units (s : String) : JSString := s.toList.map (fun c => UInt16.ofNat c.toNat)

/-- Math min/max keep the ECMAScript signed-zero tie rule and propagate NaN. -/
def numberExtremum (minimum : Bool) (a b : Float.Model) : Float.Model :=
  if a.isNaN || b.isNaN then Float.Model.nan
  else if a == Float.Model.ofNat 0 && b == Float.Model.ofNat 0 then
    let negative := if minimum then a.toBits.toNat.testBit 63 || b.toBits.toNat.testBit 63
      else a.toBits.toNat.testBit 63 && b.toBits.toNat.testBit 63
    if negative then -(Float.Model.ofNat 0) else Float.Model.ofNat 0
  else if (if minimum then a < b else b < a) then a else b

def extremum (minimum : Bool) (args : List Value) : Result Value := do
  let values ← args.mapM fun value => match value with
    | .number x => pure x
    | _ => throw (.typeError "Math.min/max arguments must be numbers")
  return .number (values.foldl (numberExtremum minimum)
    (if minimum then Float.Model.inf else -Float.Model.inf))

/-- Search positions use clamping, unlike slice's relative negative indices. -/
def position (value : Value) (length : Nat) : Nat :=
  match value with
  | .number x => min length (x.unpack.toInt 0 length).toNat
  | _ => 0

def stringIndex (haystack needle : JSString) (start : Nat) : Option Nat :=
  ((List.range (haystack.length + 1 - start)).map (start + ·)).find?
    (fun i => needle.isPrefixOf (haystack.drop i))

def stringSearch (haystack : JSString) (name : String) (needle : JSString) (pos : Nat) : Value :=
  match name with
  | "startsWith" => .boolean (needle.isPrefixOf (haystack.drop pos))
  | "endsWith" => .boolean (needle.length ≤ pos && needle == (haystack.take pos).drop (pos - needle.length))
  | "includes" => .boolean (stringIndex haystack needle pos).isSome
  | _ => .number (Float.Model.ofInt ((stringIndex haystack needle pos).map Int.ofNat |>.getD (-1)))

private def decimalRatio (p q : Nat) (e : Int) : Nat × Nat :=
  if e < 0 then (p * 10 ^ e.natAbs, q) else (p, q * 10 ^ e.toNat)

private def trimDecimal : Nat → Nat → Int → Nat × Int
  | 0, n, e => (n, e)
  | fuel + 1, n, e =>
    if n > 0 && n % 10 == 0 then trimDecimal fuel (n / 10) (e + 1) else (n, e)

/-- Find the closest shortest decimal that rounds back to this positive binary64.
Both adjacent integers are considered because a rounding interval can be asymmetric. -/
private def shortestDecimal (value : Float.Model) (p q : Nat) : Nat → Int → Nat × Int
  | 0, e =>
    let (n, d) := decimalRatio p q e
    (n / d, e)
  | fuel + 1, e =>
    let (n, d) := decimalRatio p q e
    let lo := n / d
    let rem := n % d
    let down := 2 * rem < d || (2 * rem == d && lo % 2 == 0)
    let first := if down then lo else lo + 1
    let second := if down then lo + 1 else lo
    if Float.Model.ofScientific first e == value then trimDecimal 17 first e
    else if Float.Model.ofScientific second e == value then trimDecimal 17 second e
    else shortestDecimal value p q fuel (e - 1)

private def formatDecimal (n : Nat) (e : Int) : String := Id.run do
  let digits := toString n
  let count := digits.length
  let point := Int.ofNat count + e
  if 0 < point && point ≤ 21 then
    if e ≥ 0 then return digits ++ String.ofList (List.replicate e.toNat '0')
    return String.ofList (digits.toList.take point.toNat) ++ "." ++
      String.ofList (digits.toList.drop point.toNat)
  if -6 < point && point ≤ 0 then
    return "0." ++ String.ofList (List.replicate point.natAbs '0') ++ digits
  let mantissa := if count == 1 then digits else
    String.ofList (digits.toList.take 1) ++ "." ++ String.ofList (digits.toList.drop 1)
  let exponent := point - 1
  return mantissa ++ "e" ++ (if exponent ≥ 0 then "+" else "-") ++ toString exponent.natAbs

/-- Decimal Number-to-string conversion; zero loses its sign, as in JavaScript. -/
def numberString (value : Float.Model) : JSString := units <| match value.unpack with
  | .notANumber => "NaN"
  | .infinity .positive => "Infinity"
  | .infinity .negative => "-Infinity"
  | .zero _ => "0"
  | .finite sign mantissa exponent _ => Id.run do
    let p := if exponent ≥ 0 then mantissa * 2 ^ exponent.toNat else mantissa
    let q := if exponent < 0 then 2 ^ exponent.natAbs else 1
    let guess := Int.ofNat (toString p).length - Int.ofNat (toString q).length
    let (scaled, divisor) := decimalRatio p q guess
    let order := if scaled < divisor then guess - 1 else guess
    let (n, e) := shortestDecimal value.abs p q 17 order
    return (if sign == .negative then "-" else "") ++ formatDecimal n e

def scalarString : Value → Result JSString
  | .string s => .ok s
  | .number n => .ok (numberString n)
  | .bigint n => .ok (units (toString n))
  | .boolean b => .ok (units (if b then "true" else "false"))
  | .undefined => .ok (units "undefined")
  | .null => .ok (units "null")
  | _ => .error (.typeError "string conversion requires a scalar")

def join (values : List Value) (separator : JSString) : Result JSString := do
  let strings ← values.mapM fun value => match value with
    | .undefined | .null => pure []
    | _ => scalarString value
  return (strings.intersperse separator).flatten

end Ariadne.Builtins

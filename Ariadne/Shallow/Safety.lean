import Ariadne.Shallow.Denote
import Ariadne.Shallow.Prelude.Int53

namespace Ariadne.Shallow.Safety
open Core

/-- Function values retain the guards produced by each actual invocation. Data
values keep the same representation; callback guards are never quantified over
inputs that the program does not visit. -/
abbrev Model (t : Core.Ty) (interp : Named.Interp := Named.canonical) : Type :=
  match t with
  | .unit => Unit
  | .bool => Bool
  | .int | .int53 => Int
  | .number => Float.Model
  | .string => JSString
  | .option t => Option (Model t interp)
  | .list t => List (Model t interp)
  | .map k v => k.Map (Model v interp)
  | .set k => k.Set
  | .pair a b => Model a interp × Model b interp
  | .sum a b => Sum (Model a interp) (Model b interp)
  | .named declaration => (interp declaration).Native
  | .fn a b => Model a interp → Model b interp × Bool
  | .step s r => Step (Model s interp) (Model r interp)
  | .exit s r => Exit (Model s interp) (Model r interp)

abbrev Environment (types : List Core.Ty) (interp : Named.Interp := Named.canonical) : Type :=
  match types with
  | [] => Unit
  | t :: ts => Model t interp × Environment ts interp


theorem shape_model (shape : Named.Shape) (interp : Named.Interp) :
    Model (shapeType shape) interp = shape.denote := by
  induction shape <;> simp_all [shapeType, Model, Named.Shape.denote]

def getVariable {interp : Named.Interp} : Var Γ t → Environment Γ interp → Model t interp
  | .here, env => env.1
  | .there v, env => getVariable (interp := interp) v env.2

def unary {interp : Named.Interp} : Unary a b → Model a interp → Model b interp
  | .not, a => !a
  | .intNeg, a => -a
  | .intToInt53, a => a
  | .int53ToInt, a => a
  | .int53ToNumber, a => Float.Model.ofInt a
  | .intSafe, a => decide (-9007199254740991 ≤ a ∧ a ≤ 9007199254740991)
  | .intAbs, a => Int.ofNat a.natAbs
  | .lengthInt53, xs => Int.ofNat xs.length
  | @Unary.mapSizeInt53 k _, value => match k with
    | .number => Int.ofNat (NumberMap.size value)
    | .int | .int53 | .string | .bool => Int.ofNat (JSMap.size value)
  | @Unary.setSizeInt53 k, value => match k with
    | .number => Int.ofNat (NumberSet.size value)
    | .int | .int53 | .string | .bool => Int.ofNat (JSSet.size value)
  | .numNeg, a => -a
  | .numTrunc, a => Builtins.numberTrunc a
  | .numFloor, a => Builtins.numberFloor a
  | .numAbs, a => a.abs
  | .intToNumber, a => Float.Model.ofInt a
  | .isSome, a => a.isSome
  | .length, xs => Float.Model.ofNat xs.length
  | .reverse, xs => xs.reverse
  | @Unary.mapSize k _, value => match k with
    | .number => Float.Model.ofNat (NumberMap.size value)
    | .int | .int53 | .string | .bool => Float.Model.ofNat (JSMap.size value)
  | @Unary.mapKeys k _, value => match k with
    | .number => NumberMap.keys value
    | .int | .int53 | .string | .bool => JSMap.keys value
  | @Unary.mapValues k _, value => match k with
    | .number => NumberMap.values value
    | .int | .int53 | .string | .bool => JSMap.values value
  | @Unary.mapEntries k _, value => match k with
    | .number => NumberMap.entries value
    | .int | .int53 | .string | .bool => JSMap.entries value
  | @Unary.setSize k, value => match k with
    | .number => Float.Model.ofNat (NumberSet.size value)
    | .int | .int53 | .string | .bool => Float.Model.ofNat (JSSet.size value)
  | @Unary.setValues k, value => match k with
    | .number => NumberSet.values value
    | .int | .int53 | .string | .bool => JSSet.values value
  | @Unary.setEntries k, value => match k with
    | .number => NumberSet.entries value
    | .int | .int53 | .string | .bool => JSSet.entries value

def binary {interp : Named.Interp} : Binary a b c → Model a interp → Model b interp → Model c interp
  | .guard, _, b => b
  | .intTdiv, a, b => Int.tdiv a b
  | .intFdiv, a, b => Int.fdiv a b
  | .intTmod, a, b => Int.tmod a b
  | .numBitsEq, a, b => a.toBits == b.toBits
  | .int53Range, a, b => Loop.integers a b
  | .intAdd, a, b => a + b
  | .intSub, a, b => a - b
  | .intMul, a, b => a * b
  | .intEq, a, b => a == b
  | .intLt, a, b => decide (a < b)
  | .intLe, a, b => decide (a ≤ b)
  | .intRange, a, b => Loop.integers a b
  | .numAdd, a, b => a + b
  | .numSub, a, b => a - b
  | .numMul, a, b => a * b
  | .numDiv, a, b => a / b
  | .numMod, a, b => numberRemainder a b
  | .numEq, a, b => a == b
  | .numLt, a, b => decide (a < b)
  | .numLe, a, b => decide (a ≤ b)
  | .strAppend, a, b => a ++ b
  | .strEq, a, b => a == b
  | .strLt, a, b => compare a b == .lt
  | .strLe, a, b => compare a b != .gt
  | .boolEq, a, b => a == b
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .append, a, b => a ++ b
  | .get, xs, i => JSArray.get xs i
  | @Binary.mapGet k _, value, key => match k with
    | .number => NumberMap.get value key
    | .int | .int53 | .string | .bool => JSMap.get value key
  | @Binary.mapHas k _, value, key => match k with
    | .number => NumberMap.has value key
    | .int | .int53 | .string | .bool => JSMap.has value key
  | @Binary.mapDelete k _, value, key => match k with
    | .number => NumberMap.delete value key
    | .int | .int53 | .string | .bool => JSMap.delete value key
  | @Binary.setHas k, value, key => match k with
    | .number => NumberSet.has value key
    | .int | .int53 | .string | .bool => JSSet.has value key
  | @Binary.setAdd k, value, key => match k with
    | .number => NumberSet.add value key
    | .int | .int53 | .string | .bool => JSSet.add value key
  | @Binary.setDelete k, value, key => match k with
    | .number => NumberSet.delete value key
    | .int | .int53 | .string | .bool => JSSet.delete value key

def mapSet {interp : Named.Interp} (k : Key) {v : Core.Ty} :
    Model (.map k v) interp → Model k.type interp → Model v interp → Model (.map k v) interp :=
  match k with
  | .number => NumberMap.set
  | .int | .int53 | .string | .bool => JSMap.set


abbrev inRange := Int53.inRange

def unarySafe {interp : Named.Interp} : (op : Unary a b) → Model a interp → Bool
  | .intToInt53, value | .int53ToNumber, value | .int53ToInt, value => inRange value
  | .lengthInt53, values => inRange values.length
  | @Unary.mapSizeInt53 k _, values => match k with
    | .number => inRange (NumberMap.size values)
    | .int | .int53 | .string | .bool => inRange (JSMap.size values)
  | @Unary.setSizeInt53 k, values => match k with
    | .number => inRange (NumberSet.size values)
    | .int | .int53 | .string | .bool => inRange (JSSet.size values)
  | _, _ => true

def binarySafe {interp : Named.Interp} : Binary a b c → Model a interp → Model b interp → Bool
  | .guard, condition, _ => condition
  | .intTdiv, _, divisor | .intFdiv, _, divisor | .intTmod, _, divisor => divisor != 0
  | .int53Range, start, stop => inRange start && inRange stop
  | .append, left, right => decide (left.length + right.length < 4294967296)
  | _, _, _ => true

def call2 {α β γ : Type} (f : α → (β → γ × Bool) × Bool) (a : α) (b : β) : γ × Bool :=
  let (g, first) := f a
  let (value, last) := g b
  (value, first && last)

def call3 {α β γ δ : Type} (f : α → (β → (γ → δ × Bool) × Bool) × Bool) (a : α) (b : β) (c : γ) : δ × Bool :=
  let (g, first) := f a
  let (value, last) := call2 g b c
  (value, first && last)

def search (predicate : α → Float.Model → Bool × Bool) : List α → Nat → Option (Nat × α) × Bool
  | [], _ => (none, true)
  | x :: xs, index =>
    let (found, safe) := predicate x (Float.Model.ofNat index)
    if found then (some (index, x), safe) else
      let (result, rest) := search predicate xs (index + 1)
      (result, safe && rest)

def each (body : α → σ → Step σ τ × Bool) : List α → σ → Exit σ τ × Bool
  | [], state => (.done state, true)
  | x :: xs, state =>
    let (step, safe) := body x state
    match step with
    | .next state =>
      let (result, rest) := each body xs state
      (result, safe && rest)
    | .stop state => (.done state, safe)
    | .ret value => (.ret value, safe)

/-- A measured loop with the denotation's budget. It is safe when every body
step is safe and every continuing step strictly decreases the nonnegative
measure, which also guarantees the budget suffices. -/
def measured (measure : σ → Int × Bool) (body : σ → Step σ τ × Bool) : Nat → σ → Exit σ τ × Bool
  | 0, state => (.done state, false)
  | n + 1, state =>
    let (step, safe) := body state
    match step with
    | .next next =>
      let (before, sb) := measure state
      let (after, sa) := measure next
      let (result, rest) := measured measure body n next
      (result, safe && sb && sa && decide (after.toNat < before.toNat) && rest)
    | .stop state => (.done state, safe)
    | .ret value => (.ret value, safe)

/-- Execute the same structural control flow while collecting primitive guards.
Functions return their guards when invoked, including closures stored in joins. -/
def term {interp : Named.Interp} : Term Γ t → Environment Γ interp → Model t interp × Bool
  | .var v, env => (getVariable v env, true)
  | .unit, _ => ((), true)
  | .bool value, _ => (value, true)
  | .int value, _ => (value, true)
  | .number m e, _ => (Float.Model.ofScientific m e, true)
  | .string value, _ => (value, true)
  | .unary op a, env =>
    let (a, safe) := term (interp := interp) a env
    (unary (interp := interp) op a, safe && unarySafe (interp := interp) op a)
  | .binary op a b, env =>
    let (a, sa) := term (interp := interp) a env
    let (b, sb) := term (interp := interp) b env
    (binary (interp := interp) op a b, sa && sb && binarySafe (interp := interp) op a b)
  | .let_ _ a body, env =>
    let (a, sa) := term (interp := interp) a env
    let (value, sb) := term (interp := interp) body (a, env)
    (value, sa && sb)
  | .ite condition yes no, env =>
    let (condition, sc) := term (interp := interp) condition env
    let (value, sb) := if condition then term (interp := interp) yes env else term (interp := interp) no env
    (value, sc && sb)
  | .none, _ => (none, true)
  | .some a, env =>
    let (a, safe) := term (interp := interp) a env
    (some a, safe)
  | .optionCase option fallback body, env =>
    let (option, sa) := term (interp := interp) option env
    let (value, sb) := match option with
      | none => term (interp := interp) fallback env
      | some a => term (interp := interp) body (a, env)
    (value, sa && sb)
  | .nil, _ => ([], true)
  | .cons a b, env =>
    let (a, sa) := term (interp := interp) a env
    let (b, sb) := term (interp := interp) b env
    (a :: b, sa && sb && decide (b.length + 1 < 4294967296))
  | .pair a b, env =>
    let (a, sa) := term (interp := interp) a env
    let (b, sb) := term (interp := interp) b env
    ((a, b), sa && sb)
  | .fst a, env =>
    let (a, safe) := term (interp := interp) a env
    (a.1, safe)
  | .snd a, env =>
    let (a, safe) := term (interp := interp) a env
    (a.2, safe)
  | .inl a, env =>
    let (a, safe) := term (interp := interp) a env
    (.inl a, safe)
  | .inr a, env =>
    let (a, safe) := term (interp := interp) a env
    (.inr a, safe)
  | .sumCase value left right, env =>
    let (value, sa) := term (interp := interp) value env
    let (value, sb) := match value with
      | .inl a => term (interp := interp) left (a, env)
      | .inr b => term (interp := interp) right (b, env)
    (value, sa && sb)
  | .pack declaration value, env =>
    let (value, safe) := term (interp := interp) value env
    ((interp declaration).construct (cast (shape_model declaration.shape interp) value), safe)
  | @Term.unpack _ declaration value, env =>
    let (value, safe) := term (interp := interp) value env
    (cast (shape_model declaration.shape interp).symm ((interp declaration).destruct value), safe)
  | .lam _ body, env => ((fun value => term (interp := interp) body (value, env)), true)
  | .app f a, env =>
    let (f, sf) := term (interp := interp) f env
    let (a, sa) := term (interp := interp) a env
    let (value, sb) := f a
    (value, sf && sa && sb)
  | .closed body, _ => term (interp := interp) body ()
  | .listMap f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let results := xs.mapIdx fun index x => call2 f x (Float.Model.ofNat index)
    (results.map Prod.fst, sf && sx && results.all Prod.snd)
  | .listFilter f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let results := xs.mapIdx fun index x => (x, call2 f x (Float.Model.ofNat index))
    ((results.filter (fun result => result.2.1)).map Prod.fst, sf && sx && results.all (fun result => result.2.2))
  | .listReduce f initial xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (initial, si) := term (interp := interp) initial env
    let (xs, sx) := term (interp := interp) xs env
    let (result, safe) := xs.zipIdx.foldl (fun (acc, safe) (x, index) =>
      let (result, step) := call3 f acc x (Float.Model.ofNat index)
      (result, safe && step)) (initial, true)
    (result, sf && si && sx && safe)
  | .listSome f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let (result, safe) := search (call2 f) xs 0
    (result.isSome, sf && sx && safe)
  | .listEvery f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let (result, safe) := search (fun x index => let (value, safe) := call2 f x index; (!value, safe)) xs 0
    (result.isNone, sf && sx && safe)
  | .listFind f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let (result, safe) := search (call2 f) xs 0
    (result.map Prod.snd, sf && sx && safe)
  | .listFindIndex f xs, env =>
    let (f, sf) := term (interp := interp) f env
    let (xs, sx) := term (interp := interp) xs env
    let (result, safe) := search (call2 f) xs 0
    ((result.map fun result => Float.Model.ofNat result.1).getD (Float.Model.ofInt (-1)), sf && sx && safe)
  | .listSlice xs start stop, env =>
    let (xs, sx) := term (interp := interp) xs env
    let (start, sa) := term (interp := interp) start env
    let (stop, sb) := term (interp := interp) stop env
    (JSArray.slice xs start stop, sx && sa && sb)
  | @Term.mapEmpty _ k _, _ => (Key.mapEmpty k, true)
  | @Term.setEmpty _ k, _ => (Key.setEmpty k, true)
  | @Term.mapSet _ k _ m key value, env =>
    let (m, sm) := term (interp := interp) m env
    let (key, sk) := term (interp := interp) key env
    let (value, sv) := term (interp := interp) value env
    (mapSet (interp := interp) k m key value, sm && sk && sv)
  | .next value, env =>
    let (value, safe) := term (interp := interp) value env
    (.next value, safe)
  | .stop value, env =>
    let (value, safe) := term (interp := interp) value env
    (.stop value, safe)
  | .ret value, env =>
    let (value, safe) := term (interp := interp) value env
    (.ret value, safe)
  | .each xs initial body, env =>
    let (xs, sx) := term (interp := interp) xs env
    let (initial, si) := term (interp := interp) initial env
    let (body, sb) := term (interp := interp) body env
    let (result, safe) := each (call2 body) xs initial
    (result, sx && si && sb && safe)
  | .measured measure initial body, env =>
    let (measure, sm) := term (interp := interp) measure env
    let (initial, si) := term (interp := interp) initial env
    let (body, sb) := term (interp := interp) body env
    let (start, ss) := measure initial
    let (result, safe) := measured measure body (start.toNat + 1) initial
    (result, sm && si && sb && ss && safe)
  | .exitCase value done returned, env =>
    let (value, sv) := term (interp := interp) value env
    let (done, sd) := term (interp := interp) done env
    let (returned, sr) := term (interp := interp) returned env
    let (value, sb) := match value with
      | .done state => done state
      | .ret result => returned result
    (value, sv && sd && sr && sb)

def dataType : Core.Ty → Bool
  | .fn .. | .step .. | .exit .. => false
  | .option a | .list a | .map _ a => dataType a
  | .pair a b | .sum a b => dataType a && dataType b
  | _ => true

theorem data_model (t : Core.Ty) (interp : Named.Interp) (data : dataType t = true) :
    Model t interp = t.denote interp := by
  induction t <;> simp_all [dataType, Model, Core.Ty.denote]

def liftEnvironment {interp : Named.Interp} (types : List Core.Ty)
    (data : types.all dataType = true) (env : Core.Env types interp) : Environment types interp :=
  match types with
  | [] => ()
  | t :: ts =>
    have h : dataType t = true ∧ ts.all dataType = true := by simpa using data
    (cast (data_model t interp h.1).symm env.1, liftEnvironment ts h.2 env.2)

def validKey : (k : Key) → k.denote → Bool
  | .int53, value => inRange value
  | _, _ => true

def validShape : (shape : Named.Shape) → shape.denote → Bool
  | .int53, value => inRange value
  | .option a, value => value.all (validShape a)
  | .list a, values => decide (values.length < 4294967296) && values.all (validShape a)
  | .map k v, values =>
    let entries : List (k.denote × v.denote) := match k with
      | .number => NumberMap.entries values
      | .int | .int53 | .string | .bool => JSMap.entries values
    inRange entries.length && entries.all (fun (key, value) => validKey k key && validShape v value)
  | .set k, values =>
    let values : List k.denote := match k with
      | .number => NumberSet.values values
      | .int | .int53 | .string | .bool => JSSet.values values
    inRange values.length && values.all (validKey k)
  | .pair a b, (x,y) => validShape a x && validShape b y
  | .sum a b, value => value.elim (validShape a) (validShape b)
  | _, _ => true

def valid {interp : Named.Interp} : (t : Core.Ty) → t.denote interp → Bool
  | .int53, value => inRange value
  | .option a, value => value.all (valid a)
  | .list a, values => decide (values.length < 4294967296) && values.all (valid a)
  | .map k v, values =>
    let entries : List (k.denote × v.denote interp) := match k with
      | .number => NumberMap.entries values
      | .int | .int53 | .string | .bool => JSMap.entries values
    inRange entries.length && entries.all (fun (key, value) => validKey k key && valid v value)
  | .set k, values =>
    let values : List k.denote := match k with
      | .number => NumberSet.values values
      | .int | .int53 | .string | .bool => JSSet.values values
    inRange values.length && values.all (validKey k)
  | .pair a b, (x,y) => valid a x && valid b y
  | .sum a b, value => value.elim (valid a) (valid b)
  | .named declaration, value => validShape declaration.shape ((interp declaration).destruct value)
  | _, _ => true

def validEnvironment {interp : Named.Interp} : (types : List Core.Ty) → Core.Env types interp → Bool
  | [], _ => true
  | t :: ts, (value, rest) => valid t value && validEnvironment ts rest

abbrev function {interp : Named.Interp} (f : Core.Function) (data : f.params.all dataType = true)
    (env : Core.Env f.params interp) : Prop :=
  validEnvironment f.params env = true ∧
    (term (interp := interp) f.body (liftEnvironment f.params data env)).2 = true

end Ariadne.Shallow.Safety

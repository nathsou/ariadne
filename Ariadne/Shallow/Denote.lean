import Ariadne.Shallow.Core

namespace Ariadne.Shallow
open Core

def Denote.unary : Unary a b → a.denote → b.denote
  | .not, a => !a
  | .intNeg, a => -a
  | .numNeg, a => -a
  | .isSome, a => a.isSome
  | .length, xs => Float.Model.ofNat xs.length
  | .reverse, xs => xs.reverse
  | @Unary.mapSize k _, value => match k with
    | .number => Float.Model.ofNat (NumberMap.size value)
    | .int | .string | .bool => Float.Model.ofNat (JSMap.size value)
  | @Unary.mapKeys k _, value => match k with
    | .number => NumberMap.keys value
    | .int | .string | .bool => JSMap.keys value
  | @Unary.mapValues k _, value => match k with
    | .number => NumberMap.values value
    | .int | .string | .bool => JSMap.values value
  | @Unary.mapEntries k _, value => match k with
    | .number => NumberMap.entries value
    | .int | .string | .bool => JSMap.entries value
  | @Unary.setSize k, value => match k with
    | .number => Float.Model.ofNat (NumberSet.size value)
    | .int | .string | .bool => Float.Model.ofNat (JSSet.size value)
  | @Unary.setValues k, value => match k with
    | .number => NumberSet.values value
    | .int | .string | .bool => JSSet.values value
  | @Unary.setEntries k, value => match k with
    | .number => NumberSet.entries value
    | .int | .string | .bool => JSSet.entries value

def Denote.binary : Binary a b c → a.denote → b.denote → c.denote
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
    | .int | .string | .bool => JSMap.get value key
  | @Binary.mapHas k _, value, key => match k with
    | .number => NumberMap.has value key
    | .int | .string | .bool => JSMap.has value key
  | @Binary.mapDelete k _, value, key => match k with
    | .number => NumberMap.delete value key
    | .int | .string | .bool => JSMap.delete value key
  | @Binary.setHas k, value, key => match k with
    | .number => NumberSet.has value key
    | .int | .string | .bool => JSSet.has value key
  | @Binary.setAdd k, value, key => match k with
    | .number => NumberSet.add value key
    | .int | .string | .bool => JSSet.add value key
  | @Binary.setDelete k, value, key => match k with
    | .number => NumberSet.delete value key
    | .int | .string | .bool => JSSet.delete value key

def Denote.mapSet (k : Key) {v : Core.Ty} :
    (Core.Ty.map k v).denote → k.type.denote → v.denote → (Core.Ty.map k v).denote :=
  match k with
  | .number => NumberMap.set
  | .int | .string | .bool => JSMap.set

/-- Structural interpretation into native Lean values. -/
def Denote.term : Term Γ t → Core.Env Γ → t.denote
  | .var v, env => v.get env
  | .unit, _ => ()
  | .bool b, _ => b
  | .int n, _ => n
  | .number m e, _ => Float.Model.ofScientific m e
  | .string s, _ => s
  | .unary op a, env => unary op (term a env)
  | .binary op a b, env => binary op (term a env) (term b env)
  | .let_ _ a b, env => term b (term a env, env)
  | .ite c a b, env => if term c env then term a env else term b env
  | .none, _ => none
  | .some a, env => some (term a env)
  | .optionCase a b c, env => (term a env).elim (term b env) (fun x => term c (x, env))
  | .nil, _ => []
  | .cons a b, env => term a env :: term b env
  | .pair a b, env => (term a env, term b env)
  | .fst a, env => (term a env).1
  | .snd a, env => (term a env).2
  | .lam _ body, env => fun x => term body (x, env)
  | .app f a, env => term f env (term a env)
  | .closed body, _ => term body ()
  | .listMap f xs, env => JSArray.map (term f env) (term xs env)
  | .listFilter f xs, env => JSArray.filter (term f env) (term xs env)
  | .listReduce f a xs, env => JSArray.reduce (term f env) (term a env) (term xs env)
  | .listSome f xs, env => JSArray.some (term f env) (term xs env)
  | .listEvery f xs, env => JSArray.every (term f env) (term xs env)
  | .listFind f xs, env => JSArray.find (term f env) (term xs env)
  | .listFindIndex f xs, env => JSArray.findIndex (term f env) (term xs env)
  | .listSlice xs a b, env => JSArray.slice (term xs env) (term a env) (term b env)
  | @Term.mapEmpty _ k _, _ => Key.mapEmpty k
  | @Term.setEmpty _ k, _ => Key.setEmpty k
  | @Term.mapSet _ k _ m key value, env => mapSet k (term m env) (term key env) (term value env)
  | .next a, env => .next (term a env)
  | .stop a, env => .stop (term a env)
  | .ret a, env => .ret (term a env)
  | .each xs init body, env => Loop.each (term xs env) (term init env) (term body env)
  | .exitCase e done ret, env => Exit.elim (term e env) (term done env) (term ret env)

def Denote.function (f : Core.Function) : Core.Env f.params → f.result.denote := term f.body

end Ariadne.Shallow

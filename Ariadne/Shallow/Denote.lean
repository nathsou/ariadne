import Ariadne.Shallow.Core

namespace Ariadne.Shallow
open Core

def Denote.unary {interp : Named.Interp} : Unary a b → a.denote interp → b.denote interp
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

def Denote.binary {interp : Named.Interp} : Binary a b c → a.denote interp → b.denote interp → c.denote interp
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

def Denote.mapSet {interp : Named.Interp} (k : Key) {v : Core.Ty} :
    (Core.Ty.map k v).denote interp → k.type.denote interp → v.denote interp → (Core.Ty.map k v).denote interp :=
  match k with
  | .number => NumberMap.set
  | .int | .int53 | .string | .bool => JSMap.set

/-- Structural interpretation into native Lean values. -/
def Denote.term {interp : Named.Interp} : Term Γ t → Core.Env Γ interp → t.denote interp
  | .var v, env => v.get (interp := interp) env
  | .unit, _ => ()
  | .bool b, _ => b
  | .int n, _ => n
  | .number m e, _ => Float.Model.ofScientific m e
  | .string s, _ => s
  | .unary op a, env => unary (interp := interp) op (term (interp := interp) a env)
  | .binary op a b, env => binary (interp := interp) op (term (interp := interp) a env) (term (interp := interp) b env)
  | .let_ _ a b, env => term (interp := interp) b (term (interp := interp) a env, env)
  | .ite c a b, env => if term (interp := interp) c env then term (interp := interp) a env else term (interp := interp) b env
  | .none, _ => none
  | .some a, env => some (term (interp := interp) a env)
  | .optionCase a b c, env => (term (interp := interp) a env).elim (term (interp := interp) b env) (fun x => term (interp := interp) c (x, env))
  | .nil, _ => []
  | .cons a b, env => term (interp := interp) a env :: term (interp := interp) b env
  | .pair a b, env => (term (interp := interp) a env, term (interp := interp) b env)
  | .fst a, env => (term (interp := interp) a env).1
  | .snd a, env => (term (interp := interp) a env).2
  | .inl a, env => .inl (term (interp := interp) a env)
  | .inr b, env => .inr (term (interp := interp) b env)
  | .sumCase value left right, env => Sum.elim
      (fun a => term (interp := interp) left (a, env))
      (fun b => term (interp := interp) right (b, env)) (term (interp := interp) value env)
  | .pack declaration value, env => (interp declaration).construct
      (cast (shape_denote declaration.shape interp) (term (interp := interp) value env))
  | @Term.unpack _ declaration value, env => cast (shape_denote declaration.shape interp).symm
      ((interp declaration).destruct (term (interp := interp) value env))
  | .lam _ body, env => fun x => term (interp := interp) body (x, env)
  | .app f a, env => term (interp := interp) f env (term (interp := interp) a env)
  | .closed body, _ => term (interp := interp) body ()
  | .listMap f xs, env => JSArray.map (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listFilter f xs, env => JSArray.filter (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listReduce f a xs, env => JSArray.reduce (term (interp := interp) f env) (term (interp := interp) a env) (term (interp := interp) xs env)
  | .listSome f xs, env => JSArray.some (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listEvery f xs, env => JSArray.every (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listFind f xs, env => JSArray.find (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listFindIndex f xs, env => JSArray.findIndex (term (interp := interp) f env) (term (interp := interp) xs env)
  | .listSlice xs a b, env => JSArray.slice (term (interp := interp) xs env) (term (interp := interp) a env) (term (interp := interp) b env)
  | @Term.mapEmpty _ k _, _ => Key.mapEmpty k
  | @Term.setEmpty _ k, _ => Key.setEmpty k
  | @Term.mapSet _ k _ m key value, env => mapSet (interp := interp) k (term (interp := interp) m env) (term (interp := interp) key env) (term (interp := interp) value env)
  | .next a, env => .next (term (interp := interp) a env)
  | .stop a, env => .stop (term (interp := interp) a env)
  | .ret a, env => .ret (term (interp := interp) a env)
  | .each xs init body, env => Loop.each (term (interp := interp) xs env) (term (interp := interp) init env) (term (interp := interp) body env)
  | .exitCase e done ret, env => Exit.elim (term (interp := interp) e env) (term (interp := interp) done env) (term (interp := interp) ret env)

def Denote.function {interp : Named.Interp} (f : Core.Function) : Core.Env f.params interp → f.result.denote interp := term (interp := interp) f.body

end Ariadne.Shallow

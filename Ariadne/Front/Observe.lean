import Ariadne.Model.Eval
import Lean.Data.Json

/-!
# Observations

JavaScript values as JSON, as `ariadne batch` and the playground exchange them with JavaScript
(`scripts/observe.mjs` is the other side).
-/

open Lean

namespace Ariadne.Front

/-- Observations as JSON; bigint and number digits are strings to keep precision. -/
partial def observe : JSValue → Json
  | .undefined => Json.arr #["undefined"]
  | .null => Json.arr #["null"]
  | .bool b => Json.arr #["bool", toJson b]
  | .number n => Json.arr #["number", toString n]
  | .bigint n => Json.arr #["bigint", toString n]
  | .string s => Json.arr #["string", Json.arr (s.toArray.map fun u => toJson u.toNat)]
  | .record kvs => Json.arr #["record", Json.arr (kvs.toArray.map fun (k, v) => Json.arr #[toJson k, observe v])]
  | .array xs => Json.arr #["array", Json.arr (xs.toArray.map observe)]
  | .closure .. | .function _ => Json.arr #["function"]
  | .map kvs => Json.arr #["map", Json.arr (kvs.toArray.map fun (k, v) =>
      Json.arr #[Json.arr (k.toArray.map fun u => toJson u.toNat), observe v])]

partial def unobserve (j : Json) : Except String JSValue := do
  let .arr parts := j | throw s!"bad value {j}"
  let tag ← parts[0]?.getD Json.null |>.getStr?
  let arg := parts[1]?.getD Json.null
  match tag with
  | "undefined" => pure .undefined
  | "null" => pure .null
  | "bool" => return .bool (← arg.getBool?)
  | "number" => match (← arg.getStr?).toInt? with
    | some n => pure (.number n)
    | none => throw "bad number"
  | "bigint" => match (← arg.getStr?).toInt? with
    | some n => pure (.bigint n)
    | none => throw "bad bigint"
  | "string" => return .string ((← arg.getArr?).toList.map fun u => (u.getNat?.toOption.getD 0).toUInt16)
  | "array" => return .array (← (← arg.getArr?).toList.mapM unobserve)
  | "record" => return .record (← (← arg.getArr?).toList.mapM fun kv => do
      let .arr #[k, v] := kv | throw "bad field"
      return (← k.getStr?, ← unobserve v))
  | "map" => return .map (← (← arg.getArr?).toList.mapM fun kv => do
      let .arr #[k, v] := kv | throw "bad entry"
      return ((← k.getArr?).toList.map fun u => (u.getNat?.toOption.getD 0).toUInt16, ← unobserve v))
  | t => throw s!"bad tag {t}"

def showFault : Fault → Json
  | .timeout => Json.arr #["error", "timeout"]
  | .typeError m => Json.arr #["error", s!"TypeError: {m}"]
  | .referenceError x => Json.arr #["error", s!"ReferenceError: {x}"]
  | .unsupported m => Json.arr #["error", s!"unsupported: {m}"]

end Ariadne.Front

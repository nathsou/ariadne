import Ariadne.Semantics

namespace Ariadne

/-- Tagged observations preserve values that JSON normally loses: bigint, undefined,
UTF-16 lone surrogates, NaN, infinities, and the sign of zero. -/
def observe (fuel : Nat) (state : State) (value : Value) : Lean.Json :=
  let tag := fun (name : String) (values : List Lean.Json) =>
    Lean.Json.arr ((Lean.toJson name :: values).toArray)
  match fuel with
  | 0 => tag "observation-limit" []
  | n + 1 =>
    match value with
    | .number x => tag "number" [Lean.toJson (toString x.toBits.toNat)]
    | .bigint x => tag "bigint" [Lean.toJson (toString x)]
    | .boolean x => tag "boolean" [Lean.toJson x]
    | .string xs => tag "string" [Lean.toJson (xs.map UInt16.toNat)]
    | .undefined => tag "undefined" []
    | .null => tag "null" []
    | .ref loc =>
      match state.heap[loc]? with
      | some (.array xs) => tag "array" [Lean.Json.arr ((xs.map (observe n state)).toArray)]
      | some (.map xs) => tag "map" [Lean.Json.arr ((xs.map fun (k, v) =>
          Lean.Json.arr #[observe n state k, observe n state v]).toArray)]
      | some (.record xs) => tag "record" [Lean.Json.arr ((xs.map fun (k, v) =>
          Lean.Json.arr #[Lean.toJson k, observe n state v]).toArray)]
      | _ => tag "opaque-reference" [Lean.toJson loc]
    | _ => tag "function" []

def observeResult : Result (Value × State) → Lean.Json
  | .ok (v, s) => Lean.Json.mkObj [("ok", observe 100 s v)]
  | .error error => Lean.Json.mkObj [("error", Lean.toJson (reprStr error))]

end Ariadne

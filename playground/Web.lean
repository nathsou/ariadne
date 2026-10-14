import Ariadne.Front.Validators
import Ariadne.Front.Observe
import Ariadne.Model.Store

/-!
# The playground's interface to the translator

Compiled to WebAssembly (`wasm/build.sh`) and called from the page's worker (`site/src/worker.ts`)
through `wasm/glue.c`. Each entry point takes and returns strings; results are JSON.
-/

open Lean Ariadne Ariadne.Front

namespace Ariadne.Web

/-- A type as TypeScript writes it, naming the program's named types. -/
partial def tsTy (T : Types) (τ : Ty) : String :=
  match T.named.find? (·.2 == τ) with
  | some (n, _) => n
  | none => match τ with
    | .bool => "boolean" | .int => "bigint" | .number => "number" | .string => "string"
    | .tag (.str s) => lit s
    | .tag (.bool b) => toString b
    | .lits a as => " | ".intercalate ((a :: as).map lit)
    | .option n σ => s!"{tsTy T σ} | " ++ match n with
      | .undef => "undefined" | .null => "null" | .both => "null | undefined"
    | .record fs =>
      let fields := (Fields.toList fs).map fun (f, σ) => s!"{f}: {tsTy T σ}"
      if fields.isEmpty then "{}" else "{ " ++ "; ".intercalate fields ++ " }"
    | .union key vs => " | ".intercalate ((Variants.toList vs).map fun (t, fs) => tsTy T (.record (.cons key (.tag t) fs)))
    | .array σ => let x := tsTy T σ; if (x.splitOn " | ").length > 1 then s!"({x})[]" else s!"{x}[]"
    | .map σ => s!"Map<string, {tsTy T σ}>"
where
  lit (units : List UInt16) : String :=
    leanString (String.ofList (units.map fun u => Char.ofNat u.toNat))

def hoverJson (T : Types) (h : Hover) : Json :=
  Json.mkObj <| [("start", toJson h.span.start), ("stop", toJson h.span.stop), ("kind", toJson h.kind),
    ("ts", toJson (tsTy T h.ty)), ("lean", toJson (T.lean h.ty))] ++
    (if h.name.isEmpty then [] else [("name", toJson h.name)]) ++
    (if h.term.isEmpty then [] else [("term", toJson h.term)]) ++
    (if h.safe.isEmpty then [] else [("safe", toJson h.safe)]) ++
    (if h.kind == "function" || h.kind == "method" then
      [("params", Json.arr (h.params.toArray.map fun (x, τ) =>
        Json.mkObj [("name", toJson x), ("ts", toJson (tsTy T τ)), ("lean", toJson (T.lean τ))]))]
    else [])

/-- Translate `text`, read from `path`: the generated Lean file, or the diagnostic; what the checked parts denote; and,
for an accepted program, its signatures (as `ariadne signatures` prints them) and boundary validators. -/
@[export ariadne_playground_translate]
def translateJson (text namespace_ path : String) : String :=
  let source : Parse.Source := { path, text }
  let (result, log) := translateLogged path namespace_ text
  let T := log.types.getD { aliases := [] }
  let hovers := Json.arr (log.hovers.map (hoverJson T))
  let fields := match result with
    | .ok lean =>
      let sigs := match signatures text with
        | .ok ls => Json.arr (ls.toArray.filterMap fun l => (Json.parse l).toOption)
        | .error _ => Json.arr #[]
      let checks := match validators (System.FilePath.fileName path |>.getD path) text with
        | .ok ts => toJson ts
        | .error _ => Json.null
      [("ok", toJson true), ("lean", toJson lean), ("signatures", sigs), ("validators", checks)]
    | .error d => [("ok", toJson false), ("diagnostic", d.toJson source)]
  (Json.mkObj (fields ++ [("hovers", hovers)])).compress

/-- Run one call in the model, as a line of `ariadne batch` gives it: `["f", args...]`, or
`["@m", state, args...]` for method `m` (in the store model). -/
@[export ariadne_playground_run]
def runJson (text call : String) : String :=
  let fuel := 100000
  let result : Except String Json := do
    let parsed ← match Parse.parse text >>= convertProgram with
      | .ok p => pure p
      | .error d => throw d.message
    let .arr parts ← Json.parse call | throw "expected an array"
    let f ← (parts[0]?.getD Json.null).getStr?
    let values ← (parts.toList.drop 1).mapM unobserve
    if f.startsWith "@" then
      return match runMethodStore parsed fuel (f.drop 1).toString (values.headD .undefined) values.tail with
        | .ok (v, t) => Json.arr #["method", observe v, observe t]
        | .error e => showFault e
    else
      return match run parsed fuel f values with
        | .ok v => observe v
        | .error e => showFault e
  match result with
  | .ok j => j.compress
  | .error e => (Json.arr #["error", s!"bad call: {e}"]).compress

end Ariadne.Web

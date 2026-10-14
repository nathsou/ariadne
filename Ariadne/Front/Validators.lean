import Ariadne.Front.Check

/-!
# Boundary validators

A source theorem `«f».source` assumes that `f`'s arguments represent its parameter types (`Ty.Rep`,
through `ArgsRep`). Inside the subset that holds by typing; at the boundary, where values come from
storage, the network or a caller outside the subset, it is a hypothesis. `ariadne validators FILE`
prints a TypeScript module with one guard per exported function and method: `args.f(a, b)` is true
only if the arguments represent `f`'s parameters, so that a caller can check what the theorem assumes.

The guards are sufficient, not necessary: a value they accept is represented. Numbers are safe
integers; records are plain objects whose fields, read as JavaScript reads them, are own data properties
(or absent, where the type admits `undefined`); arrays have no holes; maps are `Map`s with string keys.
This module is untrusted: the guards are tested (`scripts/validators.mjs`), not proved.
-/

namespace Ariadne.Front
open Ariadne.Parse (Checked)

/-- A TypeScript string literal (UTF-16 code units, escaped). -/
def tsString (units : List UInt16) : String :=
  "'" ++ String.join (units.map fun u =>
    if u ≥ 0x20 && u < 0x7F && u != 0x27 && u != 0x5C then (Char.ofNat u.toNat).toString
    else "\\u" ++ (let h := Nat.toDigits 16 u.toNat; String.ofList (List.replicate (4 - h.length) '0' ++ h))) ++ "'"

def tsName (s : String) : String := tsString (s.toList.flatMap Parse.utf16)

def tsTag : TagLit → String
  | .str s => tsString s
  | .bool b => toString b

mutual
  /-- A guard for `τ`: a TypeScript expression of type `Guard`. -/
  partial def tsGuard : Ty → String
    | .bool => "isBool" | .int => "isBigint" | .number => "isInt" | .string => "isString"
    | .tag t => s!"is({tsTag t})"
    | .lits a as => "oneOf([" ++ ", ".intercalate ((a :: as).map tsString) ++ "])"
    | .option n τ => s!"opt('{match n with | .undef => "undefined" | .null => "null" | .both => "both"}', {tsGuard τ})"
    | .record fs => s!"rec({tsFields fs})"
    | .union key vs => s!"union({tsName key}, [" ++ ", ".intercalate ((Variants.toList vs).map fun (t, fs) =>
        s!"[{tsTag t}, {tsFields fs}]") ++ "])"
    | .array τ => s!"arr({tsGuard τ})"
    | .map τ => s!"map({tsGuard τ})"

  partial def tsFields (fs : Fields) : String :=
    "[" ++ ", ".intercalate ((Fields.toList fs).map fun (f, τ) => s!"[{tsName f}, {tsGuard τ}]") ++ "]"
end

/-- The guards' shared definitions (exported, so that a module using few of them still compiles with
`noUnusedLocals`). -/
def validatorsRuntime : String := "export type Guard = (v: unknown) => boolean;
export type Fields = [string, Guard][];
export const isBool: Guard = v => typeof v === 'boolean';
export const isBigint: Guard = v => typeof v === 'bigint';
export const isInt: Guard = v => Number.isSafeInteger(v);
export const isString: Guard = v => typeof v === 'string';
export const is = (x: unknown): Guard => v => v === x;
export const oneOf = (xs: unknown[]): Guard => v => xs.includes(v);
export const opt = (n: 'undefined' | 'null' | 'both', g: Guard): Guard => v =>
  (v === undefined && n !== 'null') || (v === null && n !== 'undefined') || g(v);
export const plain = (v: unknown): v is Record<string, unknown> => {
  if (typeof v !== 'object' || v === null) return false;
  const p = Object.getPrototypeOf(v);
  return p === Object.prototype || p === null;
};
/** Field `f` as JavaScript reads it: an own data property, or absent (and not inherited). */
export const field = (v: object, f: string, g: Guard): boolean => {
  const d = Object.getOwnPropertyDescriptor(v, f);
  if (d === undefined) return !(f in v) && g(undefined);
  return 'value' in d && g(d.value);
};
export const rec = (fs: Fields): Guard => v => plain(v) && fs.every(([f, g]) => field(v, f, g));
export const union = (key: string, vs: [unknown, Fields][]): Guard => v =>
  plain(v) && vs.some(([t, fs]) => field(v, key, is(t)) && fs.every(([f, g]) => field(v, f, g)));
export const arr = (g: Guard): Guard => v => {
  if (!Array.isArray(v) || Object.getPrototypeOf(v) !== Array.prototype) return false;
  for (let i = 0; i < v.length; i++) {
    const d = Object.getOwnPropertyDescriptor(v, i);
    if (d === undefined || !('value' in d) || !g(d.value)) return false;
  }
  return true;
};
export const map = (g: Guard): Guard => v =>
  v instanceof Map && Object.getPrototypeOf(v) === Map.prototype && [...v].every(([k, x]) => typeof k === 'string' && g(x));
"

/-- The validators module for a file (see the module docs). -/
def validators (source text : String) : Checked String := do
  let parsed ← Parse.parse text
  let (_, fns) ← checkProgram parsed
  let entries := fns.filterMap fun c =>
    let exported := parsed.functions.any fun f => f.name == c.sig.name && f.exported
    if c.sig.name.startsWith "new " || !(exported || c.sig.method) then none else
    -- A method's first parameter is the object's state, which the class keeps; the guard checks the rest.
    let params := if c.sig.method then c.sig.params.drop 1 else c.sig.params
    let checks := params.mapIdx fun i (_, τ) => s!"{tsGuard τ}(a[{i}])"
    some s!"  {tsName c.sig.name}: (...a: unknown[]): boolean => {if checks.isEmpty then "true" else " && ".intercalate checks},"
  return s!"// Generated by ariadne from {source}. Do not edit.
// Guards for the hypotheses of the source theorems: `args.f(...)` holds only if the arguments represent
// the parameter types of `f` (for a method, after the object), as `«f».source` assumes.

{validatorsRuntime}
export const args = \{
{"\n".intercalate entries}
};
"

end Ariadne.Front

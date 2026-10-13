import V2.Front.Convert
import V2.Model.Eval
import Lean.Data.Json

/-! The `ariadne2` command line. -/

open V2 V2.Front Lean

private def usage : String :=
  "ariadne2 — TypeScript subset to Lean 4, with a general correctness theorem\n\n" ++
  "  ariadne2 batch FILE < CALLS\n" ++
  "  ariadne2 signatures FILE\n\n" ++
  "batch evaluates calls in the trusted model (no type checking): one JSON array per\n" ++
  "line, the function name then its arguments as observations, and prints one\n" ++
  "observation per line. Observations: [\"undefined\"], [\"null\"], [\"bool\", b],\n" ++
  "[\"number\", \"n\"], [\"bigint\", \"n\"], [\"string\", [code units]], [\"array\", [...]],\n" ++
  "[\"record\", [[key, value], ...]] (insertion order), [\"function\"], or [\"error\", fault]."

private def option (args : List String) (key : String) : Option String :=
  match args with
  | a :: b :: rest => if a == key then some b else option (b :: rest) key
  | _ => none

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
  | t => throw s!"bad tag {t}"

private def showFault : Fault → Json
  | .timeout => Json.arr #["error", "timeout"]
  | .typeError m => Json.arr #["error", s!"TypeError: {m}"]
  | .referenceError x => Json.arr #["error", s!"ReferenceError: {x}"]
  | .unsupported m => Json.arr #["error", s!"unsupported: {m}"]

private def report (source : V2.Parse.Source) (d : V2.Parse.Diagnostic) : IO UInt32 := do
  let (line, column) := source.position d.span.start
  IO.eprintln s!"{source.path}:{line}:{column}: error {d.code}: {d.message}"
  if let some help := d.help then IO.eprintln s!"  help: {help}"
  return 1

private def tyName : V2.Parse.Ty → String
  | .bigint => "bigint" | .boolean => "boolean" | .string => "string" | .number => "number"
  | .named n => n | _ => "other"

def main (args : List String) : IO UInt32 := do
  match args with
  | "batch" :: path :: [] =>
    let text ← IO.FS.readFile path
    let parsed ← match V2.Parse.parse text >>= convertProgram with
      | .ok p => pure p
      | .error d => return ← report { path, text } d
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.trimAscii.isEmpty then break
      let call : Except String (String × List JSValue) := do
        let .arr parts ← Json.parse line | throw "expected an array"
        let f ← (parts[0]?.getD Json.null).getStr?
        return (f, ← (parts.toList.drop 1).mapM unobserve)
      match call with
      | .ok (f, values) => stdout.putStrLn (match run parsed 100000 f values with
          | .ok v => (observe v).compress
          | .error e => (showFault e).compress)
      | .error e => IO.eprintln e; return 2
    stdout.flush
    return 0
  | "signatures" :: path :: [] =>
    let text ← IO.FS.readFile path
    match V2.Parse.parse text with
    | .error d => report { path, text } d
    | .ok parsed =>
      for f in parsed.functions do
        let params := ",".intercalate (f.params.map fun p => s!"\"{tyName p.ty}\"")
        IO.println s!"\{\"name\":\"{f.name}\",\"exported\":{f.exported},\"params\":[{params}],\"result\":\"{tyName f.result}\"}"
      return 0
  | _ => IO.eprintln usage; return 2

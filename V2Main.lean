import V2.Front.Check
import V2.Model.Eval
import Lean.Data.Json

/-! The `ariadne2` command line: translate a file, or run a function in the model. -/

open V2 V2.Front

private def usage : String :=
  "ariadne2 — TypeScript subset to Lean 4, with a general correctness theorem\n\n" ++
  "  ariadne2 translate FILE --out FILE.lean --namespace NAME\n" ++
  "  ariadne2 run FILE FUNCTION [ARG...]\n" ++
  "  ariadne2 batch FILE < CALLS\n" ++
  "  ariadne2 signatures FILE\n\n" ++
  "run evaluates FUNCTION in the trusted model (no type checking). Arguments are\n" ++
  "bigint literals (12n, -3n), true/false, or JSON strings (\"text\"). Results print as\n" ++
  "bigint:N, bool:B, string:[code units], undefined, or error:FAULT.\n" ++
  "batch reads one call per line, tab-separated: FUNCTION then arguments written\n" ++
  "i:N (bigint), b:true|false, or s:U,U,... (UTF-16 code units), and prints one result per line."

private def option (args : List String) (key : String) : Option String :=
  match args with
  | a :: b :: rest => if a == key then some b else option (b :: rest) key
  | _ => none

private def utf16 (s : String) : JSString :=
  s.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n.toUInt16]
    else let m := n - 0x10000; [(0xD800 + m / 0x400).toUInt16, (0xDC00 + m % 0x400).toUInt16]

private def parseArg (arg : String) : Except String JSValue :=
  if arg == "true" then .ok (.bool true)
  else if arg == "false" then .ok (.bool false)
  else if arg.endsWith "n" then
    match (arg.dropEnd 1).toString.toInt? with
    | some n => .ok (.bigint n)
    | none => .error s!"bad bigint argument {arg}"
  else match Lean.Json.parse arg with
    | .ok (.str s) => .ok (.string (utf16 s))
    | _ => .error s!"bad argument {arg}"

private def parseTagged (arg : String) : Except String JSValue :=
  match arg.splitOn ":" with
  | ["b", "true"] => .ok (.bool true)
  | ["b", "false"] => .ok (.bool false)
  | ["i", n] => match n.toInt? with
    | some n => .ok (.bigint n)
    | none => .error s!"bad bigint {n}"
  | ["s", ""] => .ok (.string [])
  | ["s", units] => match (units.splitOn ",").mapM String.toNat? with
    | some us => .ok (.string (us.map (·.toUInt16)))
    | none => .error s!"bad string {units}"
  | _ => .error s!"bad argument {arg}"

private def showValue : JSValue → String
  | .undefined => "undefined"
  | .bool b => s!"bool:{b}"
  | .bigint n => s!"bigint:{n}"
  | .string s => s!"string:[{",".intercalate (s.map (toString ·.toNat))}]"

private def showFault : Fault → String
  | .timeout => "error:timeout"
  | .typeError m => s!"error:TypeError:{m}"
  | .referenceError x => s!"error:ReferenceError:{x}"

private def report (source : Ariadne.Source) (d : Ariadne.Diagnostic) : IO UInt32 := do
  let (line, column) := source.position d.span.start
  IO.eprintln s!"{source.path}:{line}:{column}: error {d.code}: {d.message}"
  if let some help := d.help then IO.eprintln s!"  help: {help}"
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "translate" :: path :: rest =>
    let some out := option rest "--out" | IO.eprintln usage; return 2
    let some ns := option rest "--namespace" | IO.eprintln usage; return 2
    let text ← IO.FS.readFile path
    match translate path ns text with
    | .ok lean => IO.FS.writeFile out lean; return 0
    | .error d => report { path, text } d
  | "run" :: path :: f :: rest =>
    let text ← IO.FS.readFile path
    let parsed ← match Ariadne.parse text >>= convertProgram with
      | .ok p => pure p
      | .error d => return ← report { path, text } d
    let values ← match rest.mapM parseArg with
      | .ok vs => pure vs
      | .error e => IO.eprintln e; return 2
    match run parsed 10000 f values with
    | .ok v => IO.println (showValue v)
    | .error e => IO.println (showFault e)
    return 0
  | "batch" :: path :: [] =>
    let text ← IO.FS.readFile path
    let parsed ← match Ariadne.parse text >>= convertProgram with
      | .ok p => pure p
      | .error d => return ← report { path, text } d
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      match (line.trimAsciiEnd.toString.splitOn "\t") with
      | f :: rest =>
        match rest.mapM parseTagged with
        | .ok values => stdout.putStrLn (match run parsed 10000 f values with
            | .ok v => showValue v
            | .error e => showFault e)
        | .error e => IO.eprintln e; return 2
      | [] => pure ()
    stdout.flush
    return 0
  | "signatures" :: path :: [] =>
    let text ← IO.FS.readFile path
    match Ariadne.parse text with
    | .error d => report { path, text } d
    | .ok parsed =>
      for f in parsed.functions do
        let ty (t : Ariadne.Ty) : String := match t with
          | .bigint => "bigint" | .boolean => "boolean" | .string => "string" | _ => "other"
        let params := ",".intercalate (f.params.map fun p => s!"\"{ty p.ty}\"")
        IO.println s!"\{\"name\":\"{f.name}\",\"exported\":{f.exported},\"params\":[{params}],\"result\":\"{ty f.result}\"}"
      return 0
  | _ => IO.eprintln usage; return 2

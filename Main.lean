import Ariadne.Front.Check
import Ariadne.Model.Eval
import Ariadne.Model.Store
import Lean.Data.Json

/-! The `ariadne` command line. -/

open Ariadne Ariadne.Front Lean

private def usage : String :=
  "ariadne — TypeScript subset to Lean 4, with a general correctness theorem\n\n" ++
  "  ariadne translate FILE --out FILE.lean --namespace NAME\n" ++
  "  ariadne batch FILE < CALLS\n" ++
  "  ariadne signatures FILE\n" ++
  "  ariadne ast FILE\n\n" ++
  "batch evaluates calls in the trusted model (no type checking): one JSON array per\n" ++
  "line, the function name then its arguments as observations, and prints one\n" ++
  "observation per line. Observations: [\"undefined\"], [\"null\"], [\"bool\", b],\n" ++
  "[\"number\", \"n\"], [\"bigint\", \"n\"], [\"string\", [code units]], [\"array\", [...]],\n" ++
  "[\"record\", [[key, value], ...]] (insertion order), [\"map\", [[key units, value], ...]],\n" ++
  "[\"function\"], or [\"error\", fault]. A call [\"@m\", state, args...] runs method m on the\n" ++
  "state and prints [\"method\", result, state]."

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

/-! The converted program as JSON, for comparison with an independent converter (`scripts/crosscheck.mjs`). -/

def litJson : Lit → Json
  | .undefined => Json.arr #["undefined"]
  | .null => Json.arr #["null"]
  | .bool b => Json.arr #["bool", toJson b]
  | .number n => Json.arr #["number", toString n]
  | .bigint n => Json.arr #["bigint", toString n]
  | .string s => Json.arr #["string", Json.arr (s.toArray.map fun u => toJson u.toNat)]

def binOpName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod" | .floorDiv => "floorDiv"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .coalesce => "coalesce" | .looseEq => "looseEq" | .looseNe => "looseNe"

partial def exprJson : Ariadne.Expr → Json
  | .lit l => Json.arr #["lit", litJson l]
  | .var x => Json.arr #["var", x]
  | .unary op e => Json.arr #["unary", match op with | .not => "not" | .neg => "neg" | .inc => "inc" | .dec => "dec",
      exprJson e]
  | .binary op a b => Json.arr #["binary", binOpName op, exprJson a, exprJson b]
  | .cond c a b => Json.arr #["cond", exprJson c, exprJson a, exprJson b]
  | .call f args => Json.arr #["call", f, Json.arr (args.toArray.map exprJson)]
  | .record es => Json.arr #["record", Json.arr (es.toArray.map fun (n, e) =>
      Json.arr #[match n with | some f => toJson f | none => Json.null, exprJson e])]
  | .field e f => Json.arr #["field", exprJson e, f]
  | .array es => Json.arr #["array", Json.arr (es.toArray.map fun (sp, e) => Json.arr #[toJson sp, exprJson e])]
  | .index e i => Json.arr #["index", exprJson e, exprJson i]
  | .method e m args => Json.arr #["method", exprJson e, m, Json.arr (args.toArray.map exprJson)]
  | .arrow ps body => Json.arr #["arrow", Json.arr (ps.toArray.map toJson), exprJson body]
  | .newMap => Json.arr #["newMap"]
  | .stateGet f k => Json.arr #["stateGet", f, exprJson k]
  | .stateHas f k => Json.arr #["stateHas", f, exprJson k]
  | .stateSize f => Json.arr #["stateSize", f]
  | .stateKeys f => Json.arr #["stateKeys", f]
  | .stateValues f => Json.arr #["stateValues", f]
  | .callThis m args => Json.arr #["callThis", m, Json.arr (args.toArray.map exprJson)]

partial def stmtJson : Stmt → Json
  | .const x e => Json.arr #["const", x, exprJson e]
  | .let_ x e => Json.arr #["let", x, exprJson e]
  | .assign x e => Json.arr #["assign", x, exprJson e]
  | .ret e => Json.arr #["ret", exprJson e]
  | .ite c yes no => Json.arr #["ite", exprJson c, stmtsJson yes, stmtsJson no]
  | .block ss => Json.arr #["block", stmtsJson ss]
  | .switch e cases => Json.arr #["switch", exprJson e, Json.arr (cases.toArray.map fun (l, ss) =>
      Json.arr #[match l with | some t => exprJson t | none => Json.null, stmtsJson ss])]
  | .brk => Json.arr #["break"]
  | .cont => Json.arr #["continue"]
  | .forOf x e body => Json.arr #["forOf", x, exprJson e, stmtsJson body]
  | .forEntries i x e body => Json.arr #["forEntries", i, x, exprJson e, stmtsJson body]
  | .forRange i n body => Json.arr #["forRange", i, n, stmtsJson body]
  | .while_ c body => Json.arr #["while", exprJson c, stmtsJson body]
  | .stateSet f k v => Json.arr #["stateSet", f, exprJson k, exprJson v]
  | .stateDelete f k => Json.arr #["stateDelete", f, exprJson k]
  | .callThis m args => Json.arr #["callThisStmt", m, Json.arr (args.toArray.map exprJson)]
where stmtsJson (ss : List Stmt) : Json := Json.arr (ss.toArray.map stmtJson)

def programJson (p : Program) : Json :=
  Json.arr (p.toArray.map fun fn => Json.mkObj [("name", toJson fn.name), ("params", toJson fn.params),
    ("method", toJson fn.method), ("body", stmtJson.stmtsJson fn.body)])

private def showFault : Fault → Json
  | .timeout => Json.arr #["error", "timeout"]
  | .typeError m => Json.arr #["error", s!"TypeError: {m}"]
  | .referenceError x => Json.arr #["error", s!"ReferenceError: {x}"]
  | .unsupported m => Json.arr #["error", s!"unsupported: {m}"]

private def report (source : Ariadne.Parse.Source) (d : Ariadne.Parse.Diagnostic) : IO UInt32 := do
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
  | "batch" :: path :: [] =>
    let text ← IO.FS.readFile path
    let parsed ← match Ariadne.Parse.parse text >>= convertProgram with
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
      | .ok (f, values) =>
        -- `@m`: method `m` on the state given first; the result and the state it leaves.
        if f.startsWith "@" then
          -- In the store model (one object changed in place), which `runMethod_store` proves
          -- equal to the value model the theorems are about.
          stdout.putStrLn (match runMethodStore parsed 100000 (f.drop 1).toString (values.headD .undefined) values.tail with
            | .ok (v, t) => (Json.arr #["method", observe v, observe t]).compress
            | .error e => (showFault e).compress)
        else
          stdout.putStrLn (match run parsed 100000 f values with
            | .ok v => (observe v).compress
            | .error e => (showFault e).compress)
      | .error e => IO.eprintln e; return 2
    stdout.flush
    return 0
  | "ast" :: path :: [] =>
    let text ← IO.FS.readFile path
    match Ariadne.Parse.parse text >>= convertProgram with
    | .ok p => IO.println (programJson p).compress; return 0
    | .error d => report { path, text } d
  | "signatures" :: path :: [] =>
    let text ← IO.FS.readFile path
    match signatures text with
    | .error d => report { path, text } d
    | .ok lines =>
      for l in lines do IO.println l
      return 0
  | _ => IO.eprintln usage; return 2

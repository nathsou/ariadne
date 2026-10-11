import Ariadne

open Ariadne

private def usage : String :=
  "Ariadne 0.1.0 — TypeScript subset to Lean 4\n\n" ++
  "  ariadne check FILE [--json]\n" ++
  "  ariadne translate FILE --out FILE.lean [--namespace NAME]\n" ++
  "  ariadne certify FILE --out FILE.lean [--namespace NAME]\n" ++
  "  ariadne eval FILE FUNCTION [FUEL]\n" ++
  "  ariadne explain CODE\n\n" ++
  "eval invokes a zero-argument function. Fuel exhaustion is inconclusive.\n" ++
  "certify checks source/model correspondence, not termination or runtime safety."

private def option (args : List String) (key : String) : Option String :=
  match args with
  | a :: b :: rest => if a == key then some b else option (b :: rest) key
  | _ => none

private def explain (code : String) : String :=
  match code with
  | "A1001" => "Recognized language construct or builtin outside the supported subset. See docs/LANGUAGE.md."
  | "A1005" => "A newline after return changes JavaScript behavior. Put the expression on the return line."
  | "A2002" => "Type mismatch. Ariadne requires explicit conversions and handles missing values explicitly."
  | "A3001" => "Ownership violation. Reference aliases, escaping borrows, or unsupported nested references were detected."
  | "A3002" => "Mutation conflicts with a traversal's shared access. Use another collection or mutate outside the callback."
  | "A3003" => "A callback calls a function whose effects are not summarized. Inline the operation or move the call outside the callback."
  | "A3004" => "The operation could invalidate the controlled-runtime contract, such as modifying prototypes or shadowing intrinsics."
  | _ => "See docs/DIAGNOSTICS.md for diagnostic families and examples."

private def process (args : List String) : IO UInt32 := do
  if args.isEmpty || args == ["--help"] || args == ["--version"] then
    IO.println usage
    return 0
  if let ["explain", code] := args then
    IO.println (explain code)
    return 0
  let command := args[0]!
  let some path := args[1]? | IO.eprintln usage; return 2
  if !["check", "translate", "certify", "eval"].contains command then
    IO.eprintln usage
    return 2
  if (System.FilePath.mk path).extension != some "ts" then
    IO.eprintln "error[A1001]: inputs must be TypeScript files with the .ts extension"
    return 2
  if command == "check" && args.drop 2 != [] && args.drop 2 != ["--json"] then
    IO.eprintln "check accepts only FILE and optional --json"
    return 2
  if command == "eval" && (args.length < 3 || args.length > 4) then
    IO.eprintln usage
    return 2
  let text ← IO.FS.readFile (System.FilePath.mk path)
  let source : Source := { path, text }
  let program ← match frontend text with
    | .ok p => pure p
    | .error d =>
      if args.contains "--json" then IO.println ((d.toJson source).compress)
      else IO.eprint (d.render source)
      return 1
  if command == "check" then
    if args.contains "--json" then
      IO.println ((Lean.Json.mkObj [("status", Lean.toJson "accepted"), ("file", Lean.toJson path),
        ("certified", Lean.toJson false)]).compress)
    else IO.println s!"Accepted {path} ({program.functions.length} functions). Translation has not been certified."
    return 0
  if command == "eval" then
    let some name := args[2]? | IO.eprintln usage; return 2
    let some fuel := (args[3]?.getD "10000").toNat?
      | IO.eprintln "Fuel must be a nonnegative integer"; return 2
    let some f := program.functions.find? (fun f => f.name == name)
      | IO.eprintln s!"Unknown function: {name}"; return 2
    if !f.params.isEmpty then IO.eprintln "eval requires a zero-argument entry function"; return 2
    let result := runState program name fuel []
    IO.println ((observeResult result).compress)
    return if result.isOk then 0 else 1
  let some out := option args "--out" | IO.eprintln "Missing --out FILE.lean"; return 2
  let namespace_ := (option args "--namespace").getD "Translated"
  if namespace_.isEmpty || !(namespace_.toList.all fun c => c.isAlphanum || c == '_') ||
      !(namespace_.toList.head?.any Char.isAlpha) then
    IO.eprintln "Namespace must start with a letter and contain only letters, digits, and underscores."
    return 2
  let outputPath : System.FilePath := out
  if outputPath.extension != some "lean" then
    IO.eprintln "Output must have the .lean extension"
    return 2
  if ← outputPath.pathExists then
    if (← IO.FS.realPath outputPath) == (← IO.FS.realPath path) then
      IO.eprintln "Refusing to overwrite the TypeScript source"
      return 2
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath (emit text program namespace_)
  if command == "translate" then
    IO.println s!"Wrote {out}. This candidate has not been kernel-checked."
    return 0
  let result ← IO.Process.output { cmd := "lake", args := #["env", "lean", out] }
  if result.exitCode != 0 then
    IO.eprintln s!"error[A4001]: generated artifact failed kernel checking: {out}"
    IO.eprint result.stdout
    IO.eprint result.stderr
    return 1
  IO.println s!"Certified source/model correspondence: {out}"
  return 0

def main (args : List String) : IO UInt32 := do
  try process args
  catch error =>
    IO.eprintln s!"error[A9000]: {error}"
    return 2

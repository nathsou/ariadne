import Ariadne

open Ariadne

private def usage : String :=
  "Ariadne 0.2.0 — TypeScript subset to Lean 4\n\n" ++
  "  ariadne check FILE [--json]\n" ++
  "  ariadne translate FILE --out FILE.lean [--namespace NAME]\n" ++
  "  ariadne certify FILE --out FILE.lean [--namespace NAME]\n" ++
  "  ariadne compile FILE FUNCTION --out FILE.lean [--namespace NAME] [--json]\n" ++
  "  ariadne extract FILE --out FILE.lean [--namespace NAME] [--json] [--no-check]\n" ++
  "  ariadne eval FILE FUNCTION [FUEL]\n" ++
  "  ariadne explain CODE\n\n" ++
  "eval invokes a zero-argument function. Fuel exhaustion is inconclusive.\n" ++
  "certify checks source/model correspondence, not termination or runtime safety."

private def option (args : List String) (key : String) : Option String :=
  match args with
  | a :: b :: rest => if a == key then some b else option (b :: rest) key
  | _ => none

private def validOutputOptions (args : List String) (seen : List String := []) : Bool :=
  match args with
  | [] => true
  | flag :: value :: rest =>
    ["--out", "--namespace"].contains flag && !seen.contains flag &&
      !value.startsWith "--" && validOutputOptions rest (flag :: seen)
  | _ => false

private def explain (code : String) : String :=
  match code with
  | "A5000" => "Shallow extraction is not available for this program yet. Use certify for the operational model."
  | "A5101" => "This construct needs a termination measure or is outside the shallow fragment."
  | "A5102" => "Ownership is insufficient to give this program value semantics."
  | "A5103" => "Shallow callbacks must be pure."
  | "A5104" => "This builtin has no shallow model yet."
  | "A4101" => "This accepted TypeScript construct is outside the scalar compiler backend. Use translate/certify for an operational model."
  | "A4102" => "Scalar compilation exceeded its nesting budget. Simplify deeply nested blocks or expressions."
  | "A4103" => "The selected compiler entry point does not exist in this source file."
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
  if !["check", "translate", "certify", "compile", "extract", "eval"].contains command then
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
  if (command == "translate" || command == "certify") && !validOutputOptions (args.drop 2) then
    IO.eprintln "Expected --out FILE.lean and optional --namespace NAME, without duplicate options"
    return 2
  if command == "compile" then
    let options := args.drop 3
    if args.length < 3 || (args[2]!).startsWith "--" ||
        (options.filter (· == "--json")).length > 1 ||
        !validOutputOptions (options.filter (· != "--json")) then
      IO.eprintln "Expected compile FILE FUNCTION --out FILE.lean [--namespace NAME] [--json]"
      return 2
  if command == "extract" then
    let options := args.drop 2
    if (options.filter (· == "--json")).length > 1 ||
        (options.filter (· == "--no-check")).length > 1 ||
        !validOutputOptions (options.filter (fun flag => flag != "--json" && flag != "--no-check")) then
      IO.eprintln "Expected extract FILE --out FILE.lean [--namespace NAME] [--json] [--no-check]"
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
  let artifact ← if command == "compile" then
    match emitCompiled text program args[2]! namespace_ with
    | .ok artifact => pure artifact
    | .error d =>
      if args.contains "--json" then IO.println ((d.toJson source).compress)
      else IO.eprint (d.render source)
      return 1
    else if command == "extract" then
      match Shallow.emit text program namespace_ with
      | .ok artifact => pure artifact
      | .error d =>
        if args.contains "--json" then IO.println ((d.toJson source).compress)
        else IO.eprint (d.render source)
        return 1
    else pure (emit text program namespace_)
  if command == "extract" then
    if args.contains "--no-check" then
      if let some parent := outputPath.parent then IO.FS.createDirAll parent
      IO.FS.writeFile outputPath artifact
      IO.println s!"Wrote {out}. This shallow candidate has not been kernel-checked."
      return 0
    -- Check a temporary candidate before touching an existing output file.
    let result ← IO.FS.withTempDir fun dir => do
      let candidate := dir / "Extracted.lean"
      IO.FS.writeFile candidate artifact
      IO.Process.output { cmd := "lake", args := #["env", "lean", candidate.toString] }
    if result.exitCode != 0 then
      IO.eprintln "error[A4001]: generated shallow artifact failed kernel checking"
      IO.eprint result.stdout
      IO.eprint result.stderr
      return 1
    if let some parent := outputPath.parent then IO.FS.createDirAll parent
    IO.FS.writeFile outputPath artifact
    IO.println s!"Certified shallow denotation: {out}. Source-transfer theorems are included for proved fragments."
    return 0
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath artifact
  if command == "translate" then
    IO.println s!"Wrote {out}. This candidate has not been kernel-checked."
    return 0
  let result ← IO.Process.output { cmd := "lake", args := #["env", "lean", out] }
  if result.exitCode != 0 then
    IO.eprintln s!"error[A4001]: generated artifact failed kernel checking: {out}"
    IO.eprint result.stdout
    IO.eprint result.stderr
    return 1
  if command == "compile" then IO.println s!"Certified scalar compilation: {out}"
  else IO.println s!"Certified source/model correspondence: {out}"
  return 0

def main (args : List String) : IO UInt32 := do
  try process args
  catch error =>
    IO.eprintln s!"error[A9000]: {error}"
    return 2

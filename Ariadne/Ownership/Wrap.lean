import Ariadne.Ownership.Guard
import Ariadne.Shallow.ClassPlan

namespace Ariadne.Ownership.Wrap

open Lean in
macro "chars!" text:str : term => do
  let characters ← text.getString.toList.mapM fun character =>
    `(Char.ofNat $(Syntax.mkNumLit (toString character.toNat)))
  let characters := characters.toArray
  `([$[$characters],*])

private def joinCharacters (separator : List Char) : List (List Char) → List Char
  | [] => []
  | [value] => value
  | value :: next :: rest => value ++ separator ++ joinCharacters separator (next :: rest)

def headerCharacters : List Char :=
  chars! "// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.\n"

def header : String := "// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.\n"

theorem header_encoded : String.ofList headerCharacters = header := by kernel_rfl

private def sliceCharacters : List Char → Nat → Nat → Nat → List Char
  | [], _, _, _ => []
  | character :: rest, position, start, stop =>
    if position ≥ stop then [] else
      let remaining := sliceCharacters rest (position + character.utf8Size) start stop
      if position < start then remaining else character :: remaining

private def slice (characters : List Char) (start stop : Nat) : List Char :=
  sliceCharacters characters 0 start stop

private def guards (helperPrefix : String) (names : List String) (plan : List ArgumentCheck) : List Char :=
  plan.flatMap fun check =>
    let left := names[check.left]!.toList
    let right := names[check.right]!.toList
    let stem := helperPrefix.toList
    let tests := [chars! "(" ++ left ++ chars! " as object) === (" ++ right ++ chars! " as object)"] ++
      (if check.leftTraversal == .deep then [stem ++ chars! "contains(" ++ right ++ chars! ", " ++ left ++ chars! ")"] else []) ++
      (if check.rightTraversal == .deep then [stem ++ chars! "contains(" ++ left ++ chars! ", " ++ right ++ chars! ")"] else [])
    chars! "  if (" ++ left ++ chars! " !== null && typeof " ++ left ++ chars! " === 'object' && " ++
      right ++ chars! " !== null && typeof " ++ right ++ chars! " === 'object' && (" ++
      joinCharacters (chars! " || ") tests ++ chars! ")) {\n    throw new TypeError('overlapping borrowed arguments');\n  }\n"

private def quoteCharacters (text : String) : List Char :=
  let digits := chars! "0123456789abcdef"
  chars! "\"" ++ (text.toList.flatMap fun character =>
    if character == '"' then chars! "\\\""
    else if character == '\\' then chars! "\\\\"
    else if character.toNat < 32 || character.toNat == 8232 || character.toNat == 8233 then
      let code := character.toNat
      chars! "\\u" ++ [digits[(code / 4096) % 16]!, digits[(code / 256) % 16]!,
        digits[(code / 16) % 16]!, digits[code % 16]!]
    else [character]) ++ chars! "\""

private def helpers (helperPrefix : String) (program : Program) : List Char :=
  let stem := helperPrefix.toList
  chars! "function " ++ stem ++
  chars! "contains(target: object, value: unknown, seen: Set<object> = new Set<object>()): boolean {\n" ++
  chars! "  if (value === target) { return true; }\n" ++
  chars! "  if (value === null || typeof value !== 'object' || seen.has(value)) { return false; }\n" ++
  chars! "  seen.add(value);\n  if (Array.isArray(value)) {\n    for (const item of value) { if (" ++ stem ++
  chars! "contains(target, item, seen)) { return true; } }\n    return false;\n  }\n" ++
  chars! "  if (value instanceof Map) {\n    for (const item of value.values()) { if (" ++ stem ++
  chars! "contains(target, item, seen)) { return true; } }\n    return false;\n  }\n" ++
  chars! "  if (value instanceof Set) { return false; }\n" ++
  (program.classes.flatMap fun class_ =>
    chars! "  if (value instanceof " ++ class_.name.toList ++ chars! ") {\n" ++
    ((class_.fields.filter (!·.private_)).flatMap fun field =>
      chars! "    if (" ++ stem ++ chars! "contains(target, value[" ++ quoteCharacters field.name ++
        chars! "], seen)) { return true; }\n") ++ chars! "    return false;\n  }\n") ++
  chars! "  for (const key of Object.keys(value)) {\n    if (" ++ stem ++
  chars! "contains(target, (value as { [key: string]: unknown })[key], seen)) { return true; }\n  }\n  return false;\n}\n\n"

private structure Edit where
  start : Nat
  stop : Nat
  text : List Char

private def insertEdit (edit : Edit) : List Edit → List Edit
  | [] => [edit]
  | first :: rest =>
    if edit.start ≤ first.start then edit :: first :: rest else first :: insertEdit edit rest

private def orderEdits : List Edit → List Edit
  | [] => []
  | first :: rest => insertEdit first (orderEdits rest)

private def methodPlan (lowered : Program) (className : String)
    (method : Ariadne.Function) : Checked (List ArgumentCheck) := do
  let function := {method with
    params := {name := "this", ty := .class_ className} :: method.params
    body := ← Shallow.ClassPlan.statement className 512 method.body}
  entryPlan lowered function

/-- Generated wrappers preserve the original implementation text. Functions
delegate to a private module function; methods use an immediately invoked
lexical implementation, preserving `this` without exposing a new public method. -/
def emitCharacterData (characters : List Char) (tokens : List Token) (program : Program) : Checked (List Char) := do
  let byteLength := characters.foldl (fun length character => length + character.utf8Size) 0
  let helperPrefix := (List.range (tokens.length + 1)).findSome? fun index =>
    let candidate := s!"__ariadne{index}_"
    if tokens.any (fun token => token.text.startsWith candidate) then none else some candidate
  let some helperPrefix := helperPrefix | Check.error "A5101" "could not allocate wrapper names" {}
  let mut edits : List Edit := []
  let mut deep := false
  for function in program.functions.filter (·.exported) do
    let plan ← entryPlan program function
    if !plan.isEmpty then
      deep := deep || plan.any (fun check => check.leftTraversal == .deep || check.rightTraversal == .deep)
      let some name := tokens.find? (fun token => token.span.start ≥ function.span.stop && token.text == function.name)
        | Check.error "A5101" "missing wrapper function name" function.span
      let implementation := helperPrefix ++ function.name
      let header := slice characters function.span.start name.span.start ++ implementation.toList ++
        slice characters name.span.stop function.body.span.start
      let body := slice characters function.body.span.start function.body.span.stop
      edits := ⟨function.body.span.start, function.body.span.stop,
         chars! "{\n" ++ guards helperPrefix (function.params.map Param.name) plan ++
          chars! "  return " ++ implementation.toList ++ chars! "(" ++
          joinCharacters (chars! ", ") (function.params.map (·.name.toList)) ++ chars! ");\n}\n\n" ++
          header ++ body⟩ :: edits
  let lowered ← Shallow.ClassPlan.lower program
  for class_ in program.classes do
    for method in class_.methods do
      let plan ← methodPlan lowered class_.name method
      if !plan.isEmpty then
        deep := deep || plan.any (fun check => check.leftTraversal == .deep || check.rightTraversal == .deep)
        let body := slice characters method.body.span.start method.body.span.stop
        edits := ⟨method.body.span.start, method.body.span.stop,
           chars! "{\n" ++ guards helperPrefix ("this" :: method.params.map Param.name) plan ++
            chars! "  const " ++ helperPrefix.toList ++ chars! "implementation = () => " ++ body ++
            chars! ";\n  return " ++ helperPrefix.toList ++ chars! "implementation();\n}"⟩ :: edits
    if let some constructor_ := class_.constructor_ then
      let plan ← entryPlan lowered constructor_
      if !plan.isEmpty then
        deep := deep || plan.any (fun check => check.leftTraversal == .deep || check.rightTraversal == .deep)
        let body := slice characters constructor_.body.span.start constructor_.body.span.stop
        edits := ⟨constructor_.body.span.start, constructor_.body.span.stop,
           chars! "{\n" ++ guards helperPrefix (constructor_.params.map Param.name) plan ++
            chars! "  const " ++ helperPrefix.toList ++ chars! "implementation = () => " ++ body ++
            chars! ";\n  " ++ helperPrefix.toList ++ chars! "implementation();\n}"⟩ :: edits
  let ordered := orderEdits edits
  let mut result := headerCharacters
  if deep then result := result ++ helpers helperPrefix program
  let mut position := 0
  for edit in ordered do
    if edit.start < position || edit.stop > byteLength then
      Check.error "A5101" "overlapping or invalid wrapper source spans" {}
    result := result ++ slice characters position edit.start ++ edit.text
    position := edit.stop
  return result ++ slice characters position byteLength

def emitCharacters (characters : List Char) (tokens : List Token) (program : Program) : Checked String :=
  (emitCharacterData characters tokens program).map String.ofList

def emit (source : String) (program : Program) : Checked String := do
  let tokens ← lex source
  emitCharacters source.toList tokens.toList program

/-- Compose existing lexer/character certificates with a character-only
renderer check, without reducing the original UTF-8 decoding again. -/
theorem emit_checked {source : String} {characters : List Char} {tokens : Array Token}
    {program : Program} {rendered : List Char}
    (decoded : source.toList = characters) (lexed : lex source = .ok tokens)
    (printed : emitCharacterData characters tokens.toList program = .ok rendered) :
    emit source program = .ok (String.ofList rendered) := by
  unfold emit
  rw [lexed]
  change emitCharacters source.toList tokens.toList program = _
  rw [decoded]
  unfold emitCharacters
  rw [printed]
  rfl

end Ariadne.Ownership.Wrap

import Ariadne.Parse.Lexer

namespace Ariadne.Parse
namespace Parser

structure State where
  tokens : Array Token
  position : Nat := 0
  deriving Inhabited

abbrev P := StateT State Checked

def peek : P Token := do
  let s ← get
  return s.tokens[s.position]?.getD { text := "<eof>", span := {} }

def pop : P Token := do
  let t ← peek
  modify fun s => { s with position := s.position + 1 }
  return t

def isNext (text : String) : P Bool := return (← peek).text == text

def accept (text : String) : P Bool := do
  if ← isNext text then let _ ← pop; return true
  else return false

def fail (code message : String) (t : Token) (help : Option String := none) : P α :=
  throw { code, message, span := t.span, help }

def expect (text : String) : P Token := do
  let t ← peek
  if t.text == text then pop
  else fail "A1000" s!"expected '{text}', found '{t.text}'" t

def identifier : P Token := do
  let t ← peek
  if t.text.toList.head?.any (fun c => c.isAlpha || c == '_' || c == '$') &&
      !["return", "if", "else", "while", "for", "const", "let", "function", "new",
        "true", "false", "null", "undefined", "break", "continue", "class", "interface",
        "enum", "namespace", "try", "catch", "throw", "switch", "case", "default", "do",
        "with", "var", "debugger", "import", "export", "extends", "implements", "in",
        "instanceof", "this", "super", "delete", "typeof", "void", "yield", "await",
        "static", "private", "protected", "public", "package"].contains t.text then pop
  else fail "A1000" "expected an identifier" t

/-- Property names may be keywords, unlike variable bindings. -/
def propertyName : P Token := do
  let t ← peek
  if t.text.toList.head?.any (fun c => c.isAlpha || c == '_' || c == '$') then pop
  else fail "A1000" "expected a property name" t

def unsupported (t : Token) : P α :=
  fail "A1001" s!"'{t.text}' is outside the supported TypeScript subset" t
    (some "See docs/LANGUAGE.md for supported constructs and alternatives.")

def budget : P α := do
  fail "A1002" "parser nesting/resource limit exceeded" (← peek)

def many (fuel : Nat) (close : String) (item : P α) : P (List α) := do
  match fuel with
  | 0 => budget
  | n + 1 =>
    if ← isNext close then return []
    if ← isNext "<eof>" then let _ ← expect close; return []
    let x ← item
    return x :: (← many n close item)

def separated (fuel : Nat) (close : String) (item : P α) : P (List α) := do
  match fuel with
  | 0 => budget
  | n + 1 =>
    if ← isNext close then return []
    let x ← item
    if ← accept "," then return x :: (← separated n close item)
    return [x]

mutual
  def parseTy (fuel : Nat) : P Ty := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← pop
      let base ← match t.text with
        | "number" => pure Ty.number | "bigint" => pure Ty.bigint
        | "boolean" => pure Ty.boolean | "string" => pure Ty.string
        | "undefined" => pure Ty.undefined | "null" => pure Ty.null
        | "void" => pure Ty.void
        | "|" => parseTy n
        | "readonly" => do
          let ty ← parseTy n
          match ty with
          | .array _ | .tuple _ => pure (.readonly ty)
          | .union (.array a) b => pure (.union (.readonly (.array a)) b)
          | .union (.tuple a) b => pure (.union (.readonly (.tuple a)) b)
          | _ => fail "A1000" "readonly type modifiers require an array or tuple" t
        | "<string>" => pure (.stringLiteral (t.stringValue.getD []))
        | "Set" | "ReadonlySet" => do
          let _ ← expect "<"
          let element ← parseTy n
          let _ ← expect ">"
          pure (if t.text == "ReadonlySet" then .readonly (.set element) else .set element)
        | "any" | "unknown" | "never" | "keyof" | "typeof" => unsupported t
        | "Map" | "ReadonlyMap" => do
          let _ ← expect "<"
          let k ← parseTy n
          let _ ← expect ","
          let v ← parseTy n
          let _ ← expect ">"
          pure (if t.text == "ReadonlyMap" then .readonly (.map k v) else .map k v)
        | "[" => do
          let ts ← separated n "]" (parseTy n)
          let _ ← expect "]"
          pure (.tuple ts)
        | "{" => do
          let fields ← many n "}" do
            let ro ← accept "readonly"
            let name ← propertyName
            let optional ← accept "?"
            let _ ← expect ":"
            let ty ← parseTy n
            let ty := if optional then .union ty .undefined else ty
            let ty := if ro then .fieldReadonly ty else ty
            let _ ← accept ";"
            let _ ← accept ","
            pure (name.text, ty)
          let _ ← expect "}"
          pure (.record fields)
        | "(" => do
          let ty ← parseTy n
          let _ ← expect ")"
          pure ty
        | _ =>
          if t.text.toList.head?.any Char.isAlpha then pure (.named t.text)
          else fail "A1000" "expected a type" t
      typeTail n base

  def typeTail (fuel : Nat) (ty : Ty) : P Ty := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      if ← accept "[" then
        let _ ← expect "]"
        typeTail n (.array ty)
      else if ← accept "|" then return .union ty (← parseTy n)
      else return ty
end

/-- A parameter: `x: T`, `x?: T` (optional), or `x` (type inferred, for callbacks). -/
def parseParam (fuel : Nat) : P Param := do
  let name ← identifier
  let optional ← accept "?"
  if !(← accept ":") then
    if optional then fail "A1000" "an optional parameter needs a type" name
    return { name := name.text, ty := .named "_", span := name.span }
  let ty ← parseTy fuel
  return { name := name.text, ty := if optional then .union ty .undefined else ty, optional, span := name.span }

/-- Decimal decoding uses structural list recursion so kernel reduction does not
need the optimized string-search iterator machinery. -/
def decimalNat (digits : List Char) : Option Nat :=
  if digits.isEmpty || !digits.all Char.isDigit then none
  else some (digits.foldl (fun n c => n * 10 + c.toNat - 48) 0)

def numericLiteral (t : Token) : Checked Literal := do
  let chars := t.text.toList
  let whole := chars.takeWhile Char.isDigit
  if whole.length > 1 && whole.head? == some '0' then
    throw { code := "A1003", message := "leading-zero numeric literals are not supported", span := t.span }
  if chars.getLast? == some 'n' then
    match decimalNat (chars.take (chars.length - 1)) with
    | some n => return .bigint n
    | none => throw { code := "A1003", message := "bigint literals must be decimal integers", span := t.span }
  let tail := chars.drop whole.length
  let fraction := if tail.head? == some '.' then (tail.drop 1).takeWhile Char.isDigit else []
  let tail := if tail.head? == some '.' then tail.drop (fraction.length + 1) else tail
  let exponent ← if tail.isEmpty then pure (0 : Int) else do
    if tail.head? != some 'e' && tail.head? != some 'E' then
      throw { code := "A1003", message := "invalid numeric literal", span := t.span }
    let digits := tail.drop 1
    let negative := digits.head? == some '-'
    let digits := if negative || digits.head? == some '+' then digits.drop 1 else digits
    let some e := decimalNat digits
      | throw { code := "A1003", message := "expected digits after the numeric exponent", span := t.span }
    if e > 4096 then
      throw { code := "A1003", message := "numeric literal exponent exceeds the supported bound", span := t.span }
    pure (if negative then -(Int.ofNat e) else Int.ofNat e)
  match decimalNat (whole ++ fraction) with
  | some m => return .number m (exponent - Int.ofNat fraction.length)
  | none => throw { code := "A1003", message := "invalid numeric literal", span := t.span }

def precedence : String → Nat
  | "??" => 1 | "||" => 2 | "&&" => 3
  | "===" | "!==" | "==" | "!=" => 4
  | "<" | "<=" | ">" | ">=" => 5
  | "+" | "-" => 6
  | "*" | "/" | "%" => 7
  | _ => 0

mutual
  def expression (fuel : Nat) (minPrec : Nat := 1) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let left ← atom n
      let left ← parsePostfix n left
      let left ← binaryTail n minPrec left
      if minPrec == 1 then
        if (← accept "?") then
          let yes ← expression n
          let _ ← expect ":"
          let no ← expression n
          return .conditional left yes no left.span
      return left

  def binaryTail (fuel minPrec : Nat) (left : Expr) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      if ["**", "&", "|", "as", "instanceof", "in"].contains t.text then unsupported t
      let prec := precedence t.text
      if prec < minPrec || prec == 0 then return left
      let _ ← pop
      let right ← expression n (prec + 1)
      if t.text == "==" || t.text == "!=" then
        match right with
        | .literal .null _ => pure ()
        | _ => fail "A1001" "loose equality is supported only against null" t
      let mixes := fun e => match e with
        | .binary op _ _ _ =>
          (t.text == "??" && ["&&", "||"].contains op) ||
            (["&&", "||"].contains t.text && op == "??")
        | _ => false
      if mixes left || mixes right then
        fail "A1001" "mixing nullish and logical operators requires an intermediate variable in this subset" t
      binaryTail n minPrec (.binary t.text left right ⟨left.span.start, right.span.stop⟩)

  def parsePostfix (fuel : Nat) (left : Expr) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      if ← accept "(" then
        let args ← separated n ")" (expression n)
        let endToken ← expect ")"
        parsePostfix n (.call left args ⟨left.span.start, endToken.span.stop⟩)
      else if ← accept "." then
        let field ← propertyName
        parsePostfix n (.member left field.text ⟨left.span.start, field.span.stop⟩)
      else if ← accept "[" then
        let index ← expression n
        let endToken ← expect "]"
        parsePostfix n (.index left index ⟨left.span.start, endToken.span.stop⟩)
      else if ← isNext "!" then
        let assertion ← pop
        if assertion.lineBreak then fail "A1005" "a non-null assertion cannot follow a line break" assertion
        parsePostfix n (.unary "#nonNull" left ⟨left.span.start, assertion.span.stop⟩)
      else if ← isNext "?." then unsupported (← pop)
      else return left

  def atom (fuel : Nat) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      if ["await", "async", "function", "super", "delete", "typeof", "yield"].contains t.text then unsupported t
      let _ ← pop
      if t.text == "<template-start>" then
        return ← templateExpression n (.literal (.string (t.stringValue.getD [])) t.span)
      if t.text == "<template-middle>" || t.text == "<template-end>" then
        fail "A1000" "expected a template interpolation expression" t
      if let some units := t.stringValue then return .literal (.string units) t.span
      if t.text.toList.head?.any Char.isDigit then
        return .literal (← numericLiteral t) t.span
      match t.text with
      | "true" => return .literal (.boolean true) t.span
      | "false" => return .literal (.boolean false) t.span
      | "null" => return .literal .null t.span
      | "undefined" => return .literal .undefined t.span
      | "!" | "-" | "+" => return .unary t.text (← expression n 8) t.span
      | "(" =>
        let saved ← get
        -- Typed callbacks are unambiguous; speculative parsing never escapes on failure.
        let candidate := (do
          let params ← separated n ")" (parseParam n)
          let _ ← expect ")"
          let _ ← expect "=>"
          pure params : P (List Param)).run saved
        match candidate with
        | .ok (params, next) =>
          set next
          let body ← if ← isNext "{" then statement n else do
            let e ← expression n
            pure (.return_ e e.span)
          return .lambda params body t.span
        | .error _ =>
          let e ← expression n
          let _ ← expect ")"
          return e
      | "..." => return .spread (← expression n) t.span
      | "[" =>
        let xs ← separated n "]" (expression n)
        let endToken ← expect "]"
        return .array xs ⟨t.span.start, endToken.span.stop⟩
      | "{" =>
        let fields ← separated n "}" do
          if ← accept "..." then return ("", ← expression n)
          let field ← propertyName
          if ← accept ":" then pure (field.text, ← expression n)
          else pure (field.text, .var field.text field.span)
        let endToken ← expect "}"
        return .record fields ⟨t.span.start, endToken.span.stop⟩
      | "new" =>
        let ctor ← identifier
        if ctor.text == "Map" || ctor.text == "Set" then
          let _ ← expect "<"
          let key ← parseTy n
          let value ← if ctor.text == "Map" then do
            let _ ← expect ","
            parseTy n
            else pure Ty.undefined
          let _ ← expect ">"
          let _ ← expect "("
          let _ ← expect ")"
          return if ctor.text == "Map" then .newMap key value ctor.span else .newSet key ctor.span
        let _ ← expect "("
        let args ← separated n ")" (expression n)
        let _ ← expect ")"
        return .newClass ctor.text args ctor.span
      | _ =>
        if t.text.toList.head?.any (fun c => c.isAlpha || c == '_' || c == '$') then
          if ← accept "=>" then
            fail "A1004" "callback parameters require explicit types" t
              (some "Write '(x: bigint) => ...', for example.")
          return .var t.text t.span
        else fail "A1000" s!"expected an expression, found '{t.text}'" t

  def templateExpression (fuel : Nat) (initial : Expr) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let value ← expression n
      let part ← pop
      if part.text != "<template-middle>" && part.text != "<template-end>" then
        fail "A1000" "expected the rest of a template literal" part
      let converted := Expr.call (.var "#templateString" value.span) [value] value.span
      let result := Expr.binary "+" (.binary "+" initial converted initial.span)
        (.literal (.string (part.stringValue.getD [])) part.span) initial.span
      if part.text == "<template-end>" then return result
      templateExpression n result

  def simpleStatement (fuel : Nat) (semicolon : Bool := true) : P Stmt := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      let result ← if t.text == "let" || t.text == "const" then do
        let _ ← pop
        let name ← identifier
        let annotation ← if ← accept ":" then pure (some (← parseTy n)) else pure none
        let _ ← expect "="
        pure (.let_ (t.text == "let") name.text annotation (← expression n) t.span)
      else do
        let target ← expression n
        let op ← peek
        if ["=", "+=", "-=", "*=", "/="].contains op.text then
          let _ ← pop
          let rhs ← expression n
          if op.text == "=" then pure (.assign target rhs target.span) else
            match target with
            | .var .. => pure (.assign target
                (.binary (if op.text == "+=" then "+" else if op.text == "-=" then "-" else if op.text == "*=" then "*" else "/") target rhs op.span) target.span)
            | .member .. | .index .. =>
              pure (.update target (if op.text == "+=" then "+" else if op.text == "-=" then "-" else if op.text == "*=" then "*" else "/") rhs target.span)
            | _ => fail "A1001" "invalid compound assignment target" op
        else if op.text == "++" || op.text == "--" then
          if op.lineBreak then fail "A1005" "postfix increment cannot follow a line break" op
          let _ ← pop
          match target with
          | .var .. => pure (.assign target (.unary op.text target op.span) target.span)
          | .member .. | .index .. =>
            pure (.update target (if op.text == "++" then "+" else "-")
              (.literal (.number 1 0) op.span) target.span)
          | _ => fail "A1001" "invalid increment or decrement target" op
        else pure (.expr target target.span)
      if semicolon then let _ ← expect ";"
      return result

  def statement (fuel : Nat) : P Stmt := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      if ["async", "class", "interface", "enum", "namespace", "try", "do", "with", "var", "debugger"].contains t.text then unsupported t
      match t.text with
      | "<decreases>" =>
        let _ ← pop
        let measure ← expression n
        let _ ← expect "<decreases-end>"
        if !(← isNext "while") then fail "A1001" "a statement measure must precede while" (← peek)
        return .measured measure (← statement n) t.span
      | "{" =>
        let _ ← pop
        let body ← many n "}" (statement n)
        let endToken ← expect "}"
        return .block body ⟨t.span.start, endToken.span.stop⟩
      | "if" =>
        let _ ← pop
        let _ ← expect "("
        let condition ← expression n
        let _ ← expect ")"
        let yes ← statement n
        let no ← if ← accept "else" then statement n else pure (.block [] t.span)
        return .if_ condition yes no t.span
      | "while" =>
        let _ ← pop
        let _ ← expect "("
        let condition ← expression n
        let _ ← expect ")"
        if !(← isNext "{") then fail "A1001" "loop bodies require braces" (← peek)
        return .while_ condition (← statement n) t.span
      | "switch" =>
        let _ ← pop
        let _ ← expect "("
        let value ← expression n
        let _ ← expect ")"
        let _ ← expect "{"
        let cases ← switchCases n
        let _ ← expect "}"
        return .switch_ value cases t.span
      | "for" =>
        let _ ← pop
        let _ ← expect "("
        let saved ← get
        let candidate := (do
          let decl ← pop
          if decl.text != "let" && decl.text != "const" then fail "A1000" "expected loop binding" decl
          if ← accept "[" then
            let first ← identifier
            let _ ← expect ","
            let second ← identifier
            let _ ← expect "]"
            let _ ← expect "of"
            pure (decl.text == "let", first.text, some second.text)
          else
            let name ← identifier
            let _ ← expect "of"
            pure (decl.text == "let", name.text, none) : P (Bool × String × Option String)).run saved
        match candidate with
        | .ok ((mutable, name, second), next) =>
          set next
          let collection ← expression n
          let _ ← expect ")"
          match second with
          | none => return .forOf mutable name collection (← statement n) t.span
          | some value => return .forOfPair mutable name value collection (← statement n) t.span
        | .error _ => pure ()
        let init ← simpleStatement n
        let condition ← expression n
        let _ ← expect ";"
        if (← isNext "let") || (← isNext "const") then
          fail "A1001" "a for-loop update cannot declare a variable" (← peek)
        let update ← simpleStatement n false
        let _ ← expect ")"
        if !(← isNext "{") then fail "A1001" "loop bodies require braces" (← peek)
        return .for_ init condition update (← statement n) t.span
      | "return" =>
        let _ ← pop
        let next ← peek
        if next.lineBreak && next.text != ";" then
          fail "A1005" "line break after 'return' changes JavaScript behavior" next
            (some "Put the returned expression on the same line as 'return'.")
        let value ← if ← isNext ";" then pure (.literal .undefined t.span) else expression n
        let _ ← expect ";"
        return .return_ value t.span
      | "throw" =>
        let _ ← pop
        let next ← peek
        if next.lineBreak then
          fail "A1005" "line break after 'throw' changes JavaScript behavior" next
            (some "Put the thrown expression on the same line as 'throw'.")
        let unsupportedThrow := "only `throw new Error(\"message\")` is supported"
        if next.text != "new" then fail "A1001" unsupportedThrow next
        let _ ← pop
        let error ← peek
        if error.text != "Error" then fail "A1001" unsupportedThrow error
        let _ ← pop
        let _ ← expect "("
        let message ← peek
        let some units := message.stringValue
          | fail "A1001" "a thrown error's message must be a string literal" message
        let _ ← pop
        let _ ← expect ")"
        let _ ← expect ";"
        return .throw_ units t.span
      | "break" | "continue" =>
        let _ ← pop
        let _ ← expect ";"
        return if t.text == "break" then .break_ t.span else .continue_ t.span
      | _ => simpleStatement n

  def switchBody (fuel : Nat) : P (List Stmt) := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      if (← isNext "case") || (← isNext "default") || (← isNext "}") then return []
      let s ← statement n
      return s :: (← switchBody n)

  def switchCases (fuel : Nat) : P (List (Option Expr × List Stmt)) := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      if ← isNext "}" then return []
      let label ← if ← accept "case" then pure (some (← expression n)) else do
        let _ ← expect "default"
        pure none
      let _ ← expect ":"
      let body ← switchBody n
      return (label, body) :: (← switchCases n)
end

def function (fuel : Nat) (exported : Bool) : P Function := do
  let start ← expect "function"
  let name ← identifier
  let _ ← expect "("
  let params ← separated fuel ")" (parseParam fuel)
  let _ ← expect ")"
  let _ ← expect ":"
  let result ← parseTy fuel
  if !(← isNext "{") then let _ ← expect "{"; pure ()
  let body ← statement fuel
  return { name := name.text, params, result, body, exported, span := start.span }

def classDeclaration (fuel : Nat) : P Class := do
  let start ← expect "class"
  let name ← identifier
  let _ ← expect "{"
  let members ← many fuel "}" do
    let private_ ← accept "private"
    let readonly_ ← accept "readonly"
    let field ← propertyName
    if ← accept "(" then
      if readonly_ then unsupported field
      let params ← separated fuel ")" (parseParam fuel)
      let _ ← expect ")"
      let result ← if field.text == "constructor" then pure Ty.void else do
        let _ ← expect ":"
        parseTy fuel
      if !(← isNext "{") then let _ ← expect "{"; pure ()
      let body ← statement fuel
      pure (Sum.inr ({ name := field.text, params, result, body, span := field.span } : Function))
    else
      let ty ← if ← accept ":" then pure (some (← parseTy fuel)) else pure none
      let _ ← expect "="
      let value ← expression fuel
      let _ ← expect ";"
      pure (Sum.inl ({ name := field.text, ty, value, private_, readonly_, span := field.span } : Field))
  let _ ← expect "}"
  let fields := members.filterMap fun m => match m with | .inl f => some f | _ => none
  let methods := members.filterMap fun m => match m with | .inr f => some f | _ => none
  if (methods.filter (·.name == "constructor")).length > 1 then
    fail "A2005" "duplicate constructor" name
  return { name := name.text, fields, methods := methods.filter (·.name != "constructor"), constructor_ := methods.find? (·.name == "constructor"), span := start.span }

def declarations (fuel : Nat) (functions : List Function) (aliases : List (String × Ty))
    (classes : List Class := []) : P Program := do
  match fuel with
  | 0 => budget
  | n + 1 =>
    if ← isNext "<eof>" then return { functions := functions.reverse, aliases := aliases.reverse, classes := classes.reverse }
    let decreases ← if ← accept "<decreases>" then do
      let measure ← expression n
      let _ ← expect "<decreases-end>"
      pure (some measure)
      else pure none
    let exported ← accept "export"
    if decreases.isSome && !(← isNext "function") then
      fail "A1001" "a declaration measure must precede a function" (← peek)
    if ← accept "type" then
      let name ← identifier
      let _ ← expect "="
      let ty ← parseTy n
      let _ ← expect ";"
      declarations n functions ((name.text, ty) :: aliases) classes
    else if ← accept "interface" then
      let name ← identifier
      let ty ← parseTy n
      match ty with
      | .record _ => declarations n functions ((name.text, ty) :: aliases) classes
      | _ => fail "A1000" "expected an interface body" name
    else if ← isNext "class" then
      let c ← classDeclaration n
      declarations n functions aliases (c :: classes)
    else if ← isNext "function" then
      let f ← function n exported
      declarations n ({ f with decreases } :: functions) aliases classes
    else unsupported (← peek)

end Parser

def parse (text : String) : Checked Program := do
  let tokens ← lex text
  let (program, _) ← Parser.declarations (min 256 (tokens.size * 4 + 32)) [] [] |>.run { tokens }
  return program

end Ariadne.Parse

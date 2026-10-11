import Ariadne.Lexer

namespace Ariadne
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
      !["return", "if", "else", "while", "for", "const", "let", "function", "new", "true", "false", "null", "undefined", "break", "continue", "class", "interface", "enum", "namespace", "try", "catch", "throw", "switch", "case", "default", "do", "with", "var", "debugger", "import", "export", "extends", "implements", "in", "instanceof", "this", "super", "delete", "typeof", "void", "yield", "await", "static", "private", "protected", "public", "package"].contains t.text then pop
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
        | "any" | "unknown" | "never" | "keyof" | "typeof" => unsupported t
        | "Map" => do
          let _ ← expect "<"
          let k ← parseTy n
          let _ ← expect ","
          let v ← parseTy n
          let _ ← expect ">"
          pure (.map k v)
        | "[" => do
          let ts ← separated n "]" (parseTy n)
          let _ ← expect "]"
          pure (.tuple ts)
        | "{" => do
          let fields ← many n "}" do
            let name ← identifier
            let _ ← expect ":"
            let ty ← parseTy n
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

def parseParam (fuel : Nat) : P Param := do
  let name ← identifier
  let _ ← expect ":"
  return { name := name.text, ty := ← parseTy fuel, span := name.span }

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
  | "===" | "!==" => 4
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
      if minPrec == 1 && (← accept "?") then
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
      if ["==", "!=", "**", "&", "|", "as", "instanceof", "in"].contains t.text then unsupported t
      let prec := precedence t.text
      if prec < minPrec || prec == 0 then return left
      let _ ← pop
      let right ← expression n (prec + 1)
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
      else if ← isNext "?." then unsupported (← pop)
      else return left

  def atom (fuel : Nat) : P Expr := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      if ["await", "async", "function", "this", "super", "delete", "typeof", "yield"].contains t.text then unsupported t
      let _ ← pop
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
      | "[" =>
        let xs ← separated n "]" (expression n)
        let endToken ← expect "]"
        return .array xs ⟨t.span.start, endToken.span.stop⟩
      | "{" =>
        let fields ← separated n "}" do
          let field ← propertyName
          let _ ← expect ":"
          pure (field.text, ← expression n)
        let endToken ← expect "}"
        return .record fields ⟨t.span.start, endToken.span.stop⟩
      | "new" =>
        let ctor ← expect "Map"
        let _ ← expect "<"
        let key ← parseTy n
        let _ ← expect ","
        let value ← parseTy n
        let _ ← expect ">"
        let _ ← expect "("
        let _ ← expect ")"
        return .newMap key value ctor.span
      | _ =>
        if t.text.toList.head?.any (fun c => c.isAlpha || c == '_' || c == '$') then
          if ← accept "=>" then
            fail "A1004" "callback parameters require explicit types" t
              (some "Write '(x: bigint) => ...', for example.")
          return .var t.text t.span
        else fail "A1000" s!"expected an expression, found '{t.text}'" t

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
          if op.text != "=" then
            match target with
            | .var .. => pure ()
            | _ => fail "A1001" "compound assignments require a local variable" op (some "Use a temporary variable and a simple assignment; receivers must be evaluated once.")
          let value := if op.text == "=" then rhs else
            .binary (if op.text == "+=" then "+" else if op.text == "-=" then "-" else if op.text == "*=" then "*" else "/") target rhs op.span
          pure (.assign target value target.span)
        else if op.text == "++" || op.text == "--" then
          if op.lineBreak then fail "A1005" "postfix increment cannot follow a line break" op
          match target with
          | .var .. => pure ()
          | _ => fail "A1001" "increment and decrement require a local variable" op
          let _ ← pop
          pure (.assign target (.binary (if op.text == "++" then "+" else "-") target
            (.literal (.number 1 0) op.span) op.span) target.span)
        else pure (.expr target target.span)
      if semicolon then let _ ← expect ";"
      return result

  def statement (fuel : Nat) : P Stmt := do
    match fuel with
    | 0 => budget
    | n + 1 =>
      let t ← peek
      if ["async", "class", "interface", "enum", "namespace", "try", "throw", "switch", "do", "with", "var", "debugger"].contains t.text then unsupported t
      match t.text with
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
        if !(← isNext "{") then fail "A1001" "if branches require braces" (← peek)
        let yes ← statement n
        let no ← if ← accept "else" then do
          if !(← isNext "{") && !(← isNext "if") then
            fail "A1001" "else branches require braces" (← peek)
          statement n
        else pure (.block [] t.span)
        return .if_ condition yes no t.span
      | "while" =>
        let _ ← pop
        let _ ← expect "("
        let condition ← expression n
        let _ ← expect ")"
        if !(← isNext "{") then fail "A1001" "loop bodies require braces" (← peek)
        return .while_ condition (← statement n) t.span
      | "for" =>
        let _ ← pop
        let _ ← expect "("
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
      | "break" | "continue" =>
        let _ ← pop
        let _ ← expect ";"
        return if t.text == "break" then .break_ t.span else .continue_ t.span
      | _ => simpleStatement n
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

def declarations (fuel : Nat) (functions : List Function) (aliases : List (String × Ty)) : P Program := do
  match fuel with
  | 0 => budget
  | n + 1 =>
    if ← isNext "<eof>" then return { functions := functions.reverse, aliases := aliases.reverse }
    let exported ← accept "export"
    if ← accept "type" then
      let name ← identifier
      let _ ← expect "="
      let ty ← parseTy n
      let _ ← expect ";"
      declarations n functions ((name.text, ty) :: aliases)
    else if ← isNext "function" then
      let f ← function n exported
      declarations n (f :: functions) aliases
    else unsupported (← peek)

end Parser

def parse (text : String) : Checked Program := do
  let tokens ← lex text
  let (program, _) ← Parser.declarations (tokens.size * 4 + 32) [] [] |>.run { tokens }
  return program

end Ariadne

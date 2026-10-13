import V2.Parse.Syntax

namespace V2.Parse

structure Token where
  text : String
  span : Span
  /-- A line terminator occurs in the trivia immediately before this token. -/
  lineBreak : Bool := false
  /-- Decoded UTF-16 code units, present only for string tokens. -/
  stringValue : Option (List UInt16) := none
  deriving Repr, BEq, DecidableEq, Inhabited

def utf16 (c : Char) : List UInt16 :=
  let n := c.toNat
  if n < 65536 then [UInt16.ofNat n]
  else [UInt16.ofNat (55296 + (n - 65536) / 1024),
        UInt16.ofNat (56320 + (n - 65536) % 1024)]

private def lineTerminator (c : Char) : Bool :=
  c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029

private def whitespace (c : Char) : Bool :=
  c.isWhitespace || lineTerminator c ||
    [0xA0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
      0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x202F, 0x205F, 0x3000, 0xFEFF].contains c.toNat

private def identifierStart (c : Char) : Bool :=
  c.isAlpha && c.toNat < 128 || c == '_' || c == '$'

private def identifierRest (c : Char) : Bool := identifierStart c || c.isDigit

private def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def takeHex : Nat → List Char → Nat → Option (Nat × List Char)
  | 0, cs, n => some (n, cs)
  | k + 1, c :: cs, n => do
    let d ← hexDigit c
    takeHex k cs (n * 16 + d)
  | _, [], _ => none

private def codePoint : Nat → List Char → Nat → Nat → Option (Nat × List Char × Nat)
  | 0, _, _, _ => none
  | n + 1, c :: cs, value, count =>
    if c == '}' then
      if count > 0 && value ≤ 0x10FFFF then some (value, cs, count + 1) else none
    else do
      let digit ← hexDigit c
      let value := value * 16 + digit
      if value > 0x10FFFF then none else codePoint n cs value (count + 1)
  | _, [], _, _ => none

/-- The fuel bound is source length: each lexer step consumes at least one character. -/
private def quoted : Nat → Char → List Char → Nat → List UInt16 → Checked (List UInt16 × List Char × Nat)
  | 0, _, _, pos, _ => .error { code := "A0002", message := "unterminated string literal", span := ⟨pos, pos⟩ }
  | n + 1, quote, cs, pos, acc => do
    match cs with
    | [] => throw { code := "A0002", message := "unterminated string literal", span := ⟨pos, pos⟩ }
    | c :: rest =>
      if c == quote then return (acc.reverse, rest, pos + c.utf8Size)
      if quote != '`' && (c == '\n' || c == '\r') then
        throw { code := "A0002", message := "unescaped line break in string literal", span := ⟨pos, pos + 1⟩ }
      if c != '\\' then
        quoted n quote rest (pos + c.utf8Size) ((utf16 c).reverse ++ acc)
      else
        match rest with
        | [] => throw { code := "A0002", message := "unterminated escape sequence", span := ⟨pos, pos + 1⟩ }
        | esc :: tail =>
          if lineTerminator esc then
            let crlf := esc == '\r' && tail.head? == some '\n'
            quoted n quote (if crlf then tail.drop 1 else tail)
              (pos + 1 + esc.utf8Size + if crlf then 1 else 0) acc
          else if esc == '0' then
            if tail.head?.any Char.isDigit then
              throw { code := "A0003", message := "legacy octal escapes are not supported", span := ⟨pos, pos + 2⟩ }
            quoted n quote tail (pos + 2) (0 :: acc)
          else if esc == 'u' && tail.head? == some '{' then
            match codePoint (tail.length + 1) (tail.drop 1) 0 0 with
            | some (value, tail', count) =>
              let units := if value < 65536 then [UInt16.ofNat value] else utf16 (Char.ofNat value)
              quoted n quote tail' (pos + 3 + count) (units.reverse ++ acc)
            | none => throw { code := "A0003", message := "invalid Unicode code point escape", span := ⟨pos, pos + 3⟩ }
          else if esc == 'u' || esc == 'x' then
            let count := if esc == 'u' then 4 else 2
            match takeHex count tail 0 with
            | some (value, tail') => quoted n quote tail' (pos + count + 2) (UInt16.ofNat value :: acc)
            | none => throw { code := "A0003", message := "invalid hexadecimal string escape", span := ⟨pos, pos + 2⟩ }
          else
            let decoded ← match esc with
              | 'n' => pure '\n' | 'r' => pure '\r' | 't' => pure '\t'
              | 'b' => pure (Char.ofNat 8) | 'f' => pure (Char.ofNat 12)
              | 'v' => pure (Char.ofNat 11) | '\\' => pure '\\'
              | '\'' => pure '\'' | '"' => pure '"'
              | _ =>
                if esc.isDigit then
                  throw { code := "A0003", message := "legacy decimal escapes are not supported", span := ⟨pos, pos + 2⟩ }
                else pure esc
            quoted n quote tail (pos + 1 + esc.utf8Size) ((utf16 decoded).reverse ++ acc)

private def blockComment : Nat → List Char → Nat → Bool → Checked (List Char × Nat × Bool)
  | 0, _, pos, _ => .error { code := "A0004", message := "unterminated block comment", span := ⟨pos, pos⟩ }
  | n + 1, cs, pos, newline =>
    match cs with
    | '*' :: '/' :: rest => .ok (rest, pos + 2, newline)
    | c :: rest => blockComment n rest (pos + c.utf8Size) (newline || lineTerminator c)
    | [] => .error { code := "A0004", message := "unterminated block comment", span := ⟨pos, pos⟩ }

private def byteLength (cs : List Char) : Nat :=
  cs.foldl (fun n c => n + c.utf8Size) 0

/-- Read one cooked template segment. Interpolations are lexed by `lexGo`, which
tracks nested braces and nested templates. Raw offsets always refer to the source. -/
private def templateChunk : Nat → List Char → Nat → Nat → List Char →
    Checked (List UInt16 × List Char × Nat × Bool)
  | 0, _, _, pos, _ => .error { code := "A0002", message := "unterminated template literal", span := ⟨pos, pos⟩ }
  | n + 1, cs, start, pos, acc => do
    match cs with
    | '`' :: rest =>
      let (units, _, _) ← quoted (acc.length + 2) '`' (acc.reverse ++ ['`']) start []
      return (units, rest, pos + 1, false)
    | '$' :: '{' :: rest =>
      let (units, _, _) ← quoted (acc.length + 2) '`' (acc.reverse ++ ['`']) start []
      return (units, rest, pos + 2, true)
    | '\\' :: c :: rest => templateChunk n rest start (pos + 1 + c.utf8Size) (c :: '\\' :: acc)
    | '\r' :: '\n' :: rest => templateChunk n rest start (pos + 2) ('\n' :: acc)
    | '\r' :: rest => templateChunk n rest start (pos + 1) ('\n' :: acc)
    | c :: rest => templateChunk n rest start (pos + c.utf8Size) (c :: acc)
    | [] => throw { code := "A0002", message := "unterminated template literal", span := ⟨start, pos⟩ }

private def lexGo : Nat → List Nat → List Char → Nat → Bool → List Token → Checked (List Token)
  | 0, _, _, pos, _, _ => .error { code := "A0005", message := "lexer resource bound exceeded", span := ⟨pos, pos⟩ }
  | n + 1, templates, cs, pos, newline, acc => do
    match cs with
    | [] =>
      if !templates.isEmpty then throw { code := "A0002", message := "unterminated template interpolation", span := ⟨pos, pos⟩ }
      return (⟨"<eof>", ⟨pos, pos⟩, newline, none⟩ :: acc).reverse
    | c :: rest =>
      if whitespace c then
        return ← lexGo n templates rest (pos + c.utf8Size) (newline || lineTerminator c) acc
      if cs.take 2 == ['/', '/'] then
        let comment := cs.takeWhile (fun c => !lineTerminator c)
        return ← lexGo n templates (cs.drop comment.length) (pos + byteLength comment) newline acc
      if cs.take 2 == ['/', '*'] then
        let (tail, stop, nl) ← blockComment (cs.length + 1) (cs.drop 2) (pos + 2) newline
        let content := (cs.drop 2).take (cs.length - tail.length - 4)
        let annotation := content.dropWhile (fun c => whitespace c || c == '*')
        if annotation.take 10 == "@decreases".toList then
          let payload := annotation.drop 10
          if payload.isEmpty || !(payload.head?.any whitespace) then
            throw { code := "A1000", message := "expected an expression after @decreases", span := ⟨pos, stop⟩ }
          let offset := pos + 2 + byteLength content - byteLength annotation + 10
          let tokens ← lexGo n [] payload offset false []
          let first : Token := ⟨"<decreases>", ⟨pos, offset⟩, newline, none⟩
          let last : Token := ⟨"<decreases-end>", ⟨stop - 2, stop⟩, false, none⟩
          return ← lexGo n templates tail stop nl (last :: tokens.dropLast.reverse ++ first :: acc)
        return ← lexGo n templates tail stop nl acc
      if c == '\'' || c == '"' then
        let (units, tail, stop) ← quoted (cs.length + 1) c rest (pos + 1) []
        return ← lexGo n templates tail stop false (⟨"<string>", ⟨pos, stop⟩, newline, some units⟩ :: acc)
      if c == '`' then
        let (units, tail, stop, more) ← templateChunk (cs.length + 1) rest (pos + 1) (pos + 1) []
        return ← lexGo n (if more then 0 :: templates else templates) tail stop false
          (⟨if more then "<template-start>" else "<string>", ⟨pos, stop⟩, newline, some units⟩ :: acc)
      if c == '}' && templates.head? == some 0 then
        let (units, tail, stop, more) ← templateChunk (cs.length + 1) rest (pos + 1) (pos + 1) []
        return ← lexGo n (if more then templates else templates.drop 1) tail stop false
          (⟨if more then "<template-middle>" else "<template-end>", ⟨pos, stop⟩, newline, some units⟩ :: acc)
      if identifierStart c then
        let word := cs.takeWhile identifierRest
        let stop := pos + byteLength word
        return ← lexGo n templates (cs.drop word.length) stop false
          (⟨String.ofList word, ⟨pos, stop⟩, newline, none⟩ :: acc)
      if c.isDigit then
        let whole := cs.takeWhile Char.isDigit
        let tail := cs.drop whole.length
        let fraction := if tail.head? == some '.' then
          '.' :: ((tail.drop 1).takeWhile Char.isDigit) else []
        let tail := tail.drop fraction.length
        let exponent := if tail.head? == some 'e' || tail.head? == some 'E' then
          let sign := if (tail.drop 1).head? == some '+' || (tail.drop 1).head? == some '-' then
            (tail.drop 1).take 1 else []
          tail.take 1 ++ sign ++ ((tail.drop (1 + sign.length)).takeWhile Char.isDigit)
          else []
        let tail := tail.drop exponent.length
        let suffix := if tail.head? == some 'n' then ['n'] else []
        let word := whole ++ fraction ++ exponent ++ suffix
        let stop := pos + word.length
        return ← lexGo n templates (tail.drop suffix.length) stop false
          (⟨String.ofList word, ⟨pos, stop⟩, newline, none⟩ :: acc)
      let operators := ["===", "!==", "=>", "<=", ">=", "&&", "||", "??", "++", "--", "+=", "-=", "*=", "/=", "==", "!=", "**", "?.", "..."]
      match operators.find? (fun op => cs.take op.length == op.toList) with
      | some op =>
        lexGo n templates (cs.drop op.length) (pos + op.length) false
          (⟨op, ⟨pos, pos + op.length⟩, newline, none⟩ :: acc)
      | none =>
        if "{}()[];:,.?+-*/%!=<>|&".toList.contains c then
          let templates := match templates with
            | depth :: rest => (if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth) :: rest
            | [] => []
          lexGo n templates rest (pos + 1) false (⟨String.singleton c, ⟨pos, pos + 1⟩, newline, none⟩ :: acc)
        else throw { code := "A0001", message := s!"unexpected character '{c}'", span := ⟨pos, pos + c.utf8Size⟩ }

def lexCharacters (chars : List Char) : Checked (Array Token) :=
  (lexGo (chars.length + 1) [] chars 0 false []).map List.toArray

def lex (text : String) : Checked (Array Token) := lexCharacters text.toList

end V2.Parse

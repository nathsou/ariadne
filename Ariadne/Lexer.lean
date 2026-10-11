import Ariadne.Syntax

namespace Ariadne

structure Token where
  text : String
  span : Span
  /-- A line terminator occurs in the trivia immediately before this token. -/
  lineBreak : Bool := false
  /-- Decoded UTF-16 code units, present only for string tokens. -/
  stringValue : Option (List UInt16) := none
  deriving Repr, BEq, Inhabited

def utf16 (c : Char) : List UInt16 :=
  let n := c.toNat
  if n < 65536 then [UInt16.ofNat n]
  else [UInt16.ofNat (55296 + (n - 65536) / 1024),
        UInt16.ofNat (56320 + (n - 65536) % 1024)]

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

/-- The fuel bound is source length: each lexer step consumes at least one character. -/
private def quoted : Nat → Char → List Char → Nat → List UInt16 → Checked (List UInt16 × List Char × Nat)
  | 0, _, _, pos, _ => .error { code := "A0002", message := "unterminated string literal", span := ⟨pos, pos⟩ }
  | n + 1, quote, cs, pos, acc => do
    match cs with
    | [] => throw { code := "A0002", message := "unterminated string literal", span := ⟨pos, pos⟩ }
    | c :: rest =>
      if c == quote then return (acc.reverse, rest, pos + c.utf8Size)
      if c == '\n' || c == '\r' then
        throw { code := "A0002", message := "unescaped line break in string literal", span := ⟨pos, pos + 1⟩ }
      if c != '\\' then
        quoted n quote rest (pos + c.utf8Size) ((utf16 c).reverse ++ acc)
      else
        match rest with
        | [] => throw { code := "A0002", message := "unterminated escape sequence", span := ⟨pos, pos + 1⟩ }
        | esc :: tail =>
          if esc == 'u' || esc == 'x' then
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
              | _ => throw { code := "A0003", message := "unsupported string escape", span := ⟨pos, pos + 2⟩ }
            quoted n quote tail (pos + 2) (UInt16.ofNat decoded.toNat :: acc)

private def blockComment : Nat → List Char → Nat → Bool → Checked (List Char × Nat × Bool)
  | 0, _, pos, _ => .error { code := "A0004", message := "unterminated block comment", span := ⟨pos, pos⟩ }
  | n + 1, cs, pos, newline =>
    match cs with
    | '*' :: '/' :: rest => .ok (rest, pos + 2, newline)
    | c :: rest => blockComment n rest (pos + c.utf8Size) (newline || c == '\n' || c == '\r')
    | [] => .error { code := "A0004", message := "unterminated block comment", span := ⟨pos, pos⟩ }

private def byteLength (cs : List Char) : Nat :=
  cs.foldl (fun n c => n + c.utf8Size) 0

private def lexGo : Nat → List Char → Nat → Bool → List Token → Checked (List Token)
  | 0, _, pos, _, _ => .error { code := "A0005", message := "lexer resource bound exceeded", span := ⟨pos, pos⟩ }
  | n + 1, cs, pos, newline, acc => do
    match cs with
    | [] => return (⟨"<eof>", ⟨pos, pos⟩, newline, none⟩ :: acc).reverse
    | c :: rest =>
      if c.isWhitespace then
        return ← lexGo n rest (pos + c.utf8Size) (newline || c == '\n' || c == '\r') acc
      if cs.take 2 == ['/', '/'] then
        let comment := cs.takeWhile (fun c => c != '\n' && c != '\r')
        return ← lexGo n (cs.drop comment.length) (pos + byteLength comment) newline acc
      if cs.take 2 == ['/', '*'] then
        let (tail, stop, nl) ← blockComment (cs.length + 1) (cs.drop 2) (pos + 2) newline
        return ← lexGo n tail stop nl acc
      if c == '\'' || c == '"' then
        let (units, tail, stop) ← quoted (cs.length + 1) c rest (pos + 1) []
        return ← lexGo n tail stop false (⟨"<string>", ⟨pos, stop⟩, newline, some units⟩ :: acc)
      if c == '`' then
        throw { code := "A1001", message := "template literals are outside the supported subset", span := ⟨pos, pos + 1⟩, help := some "Use string literals and string concatenation." }
      if identifierStart c then
        let word := cs.takeWhile identifierRest
        let stop := pos + byteLength word
        return ← lexGo n (cs.drop word.length) stop false
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
        return ← lexGo n (tail.drop suffix.length) stop false
          (⟨String.ofList word, ⟨pos, stop⟩, newline, none⟩ :: acc)
      let operators := ["===", "!==", "=>", "<=", ">=", "&&", "||", "??", "++", "--", "+=", "-=", "*=", "/=", "==", "!=", "**", "?.", "..."]
      match operators.find? (fun op => cs.take op.length == op.toList) with
      | some op =>
        lexGo n (cs.drop op.length) (pos + op.length) false
          (⟨op, ⟨pos, pos + op.length⟩, newline, none⟩ :: acc)
      | none =>
        if "{}()[];:,.?+-*/%!=<>|&".contains c then
          lexGo n rest (pos + 1) false (⟨String.singleton c, ⟨pos, pos + 1⟩, newline, none⟩ :: acc)
        else throw { code := "A0001", message := s!"unexpected character '{c}'", span := ⟨pos, pos + c.utf8Size⟩ }

def lex (text : String) : Checked (Array Token) :=
  (lexGo (text.length + 1) text.toList 0 false []).map List.toArray

end Ariadne

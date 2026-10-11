import Ariadne

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Tests.Frontend
open Ariadne

theorem decimal_exponent :
    Parser.numericLiteral { text := "125e-2", span := {} } = .ok (.number 125 (-2)) := by
  kernel_rfl

theorem bigint_unbounded :
    Parser.numericLiteral { text := "123456789012345678901234567890n", span := {} } =
      .ok (.bigint 123456789012345678901234567890) := by
  kernel_rfl

theorem unicode_scalar_is_two_units : utf16 '😀' = [55357, 56832] := by kernel_rfl

theorem lexer_preserves_lone_surrogate :
    (lex "\"\\ud800\"").map (fun tokens => tokens[0]!.stringValue) = .ok (some [55296]) := by
  kernel_rfl

theorem maximal_munch :
    (lex "a===b!==c").map (fun tokens => tokens.toList.map Token.text) =
      .ok ["a", "===", "b", "!==", "c", "<eof>"] := by
  kernel_rfl

theorem unsupported_template : (lex "`text`").isOk = false := by kernel_rfl

theorem short_circuit_prevents_division_by_zero :
    (do
      let program ← frontend "function f(): boolean { return false && (1n / 0n === 0n); }"
      return run program "f" 30 []) = .ok (.ok (.boolean false)) := by
  kernel_rfl

theorem precedence_is_multiplication_first :
    (do
      let program ← frontend "function f(): bigint { return 2n + 3n * 4n; }"
      return run program "f" 30 []) = .ok (.ok (.bigint 14)) := by
  kernel_rfl

theorem traversal_rejects_receiver_mutation :
    (frontend "function f(): void { const a = [1]; a.forEach((x: number) => { a.push(x); }); }").isOk = false := by
  kernel_rfl

theorem leading_zero_rejected :
    (frontend "function f(): number { return 01; }").isOk = false := by kernel_rfl

theorem return_line_separator_rejected :
    (frontend "function f(): bigint { return\u20281n; }").isOk = false := by kernel_rfl

theorem source_position_crlf :
    ({ path := "test.ts", text := "a\r\nb" } : Source).position 3 = (2, 1) := by kernel_rfl

theorem source_position_unicode :
    ({ path := "test.ts", text := "😀\u2028x" } : Source).position 7 = (2, 1) := by kernel_rfl

theorem callback_local_return :
    (do
      let program ← frontend "function f(): bigint { const a = [3n]; const b = a.map((x: bigint) => { let y = x * x; y += 1n; return y; }); return b[0] ?? 0n; }"
      return run program "f" 60 []) = .ok (.ok (.bigint 10)) := by kernel_rfl

end Tests.Frontend

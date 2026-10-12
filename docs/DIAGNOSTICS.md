# Diagnostics

`ariadne check file.ts` prints a diagnostic code, message, source location, the
source line, a caret, related locations where available, and a suggested remedy.
`ariadne check file.ts --json` emits a single structured diagnostic and exits 1.
CLI/IO misuse exits 2. Successful operations exit 0.

```text
error[A3002]: cannot mutate 'a' while a traversal is reading it
  --> example.ts:3:36
   |
3 |   a.forEach((x: number) => { a.push(x); });
   |                                    ^
   = related: example.ts:2:3: collection declared here
   = help: Move the mutation outside the traversal, or use a separate owned collection.
```

The exact caret location follows the offending receiver's span; the example above
illustrates the format. `ariadne explain A3002` supplies a brief explanation.

| Codes | Meaning |
| --- | --- |
| A0001–A0005 | Invalid character, malformed string/escape/comment, lexer resource bound |
| A1000 | Expected a syntactic token, identifier, type, or expression |
| A1001 | Recognized construct or builtin outside the supported subset |
| A1002 | Parser nesting/resource bound |
| A1003 | Malformed or unsupported numeric literal |
| A1004 | Missing callback parameter type |
| A1005 | A line break would change JavaScript parsing/return behavior |
| A2000–A2001 | Type-checking bound, invalid/cyclic/unknown type alias |
| A2002 | Type mismatch or invalid operands |
| A2003–A2007 | Unknown name, missing annotation, duplicate declaration, unknown property, wrong arity |
| A2008–A2010 | Const reassignment, misplaced loop control, missing return |
| A3001 | Unsupported ownership or aliasing |
| A3002 | Mutation conflicts with a collection traversal |
| A3003 | Missing interprocedural callback effect information |
| A3004 | Intrinsic/prototype or reserved-name violation |
| A4001 | Generated Lean candidate failed kernel checking |
| A9000 | IO or process error |

## JSON schema, version 1

Error payloads contain `schemaVersion`, `severity`, `code`, `message`, `file`,
`startByte`, `endByte`, `line`, `column`, `notes`, `help`, and `related`. Spans are
half-open UTF-8 byte offsets; line and column are 1-based, with columns counting
Unicode scalar values. CRLF counts as one newline; CR, LF, U+2028, and U+2029 are
recognized. Editor integrations should use byte offsets, or explicitly convert to
their preferred UTF-16 indexing. Related labels contain spans and messages.

This version reports the first failure. It does not attempt recovery after an
unsupported construct, invent a replacement program, or certify a partly parsed
file. Some whole-program errors point to the start of the file. Multi-error
recovery and richer alias-expansion traces are planned extensions.

See `examples/negative/` for executable diagnostic fixtures. Their first line records
the expected stable error code; tests additionally check the JSON schema and failure
exit status. Message prose may improve without changing those codes.

## Scalar compiler diagnostics

`compile FILE FUNCTION --out FILE.lean --json` uses the same schema. `A4101`
means the frontend accepted a construct that the scalar backend cannot compile;
the diagnostic highlights the construct or parameter and suggests the operational
translator. `A4102` is the compiler nesting limit. `A4103` is a missing entry name.
These errors leave an existing output file untouched. A generated artifact that
fails kernel checking reports `A4001` and remains an uncertified candidate.
## Shallow extraction

`extract` reserves `A5xxx`. `A5000` reports an unavailable extraction backend;
`A5101` a totality refusal; `A5102` an ownership refusal; `A5103` an impure
callback; and `A5104` a builtin without a shallow model. Frontend errors retain
their original codes. Refusal leaves existing output untouched.


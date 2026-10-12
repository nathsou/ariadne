# Verified scalar compiler

`compile` selects one function from an accepted TypeScript file and emits a Lean
function assembled from `Target` combinators. It checks the artifact with the Lean
kernel before reporting success:

```sh
.lake/build/bin/ariadne compile examples/scalar/multiply.ts multiply \
  --out work/Multiply.lean --namespace Multiply
```

The output retains the source certificate and operational wrapper, and adds:

- `compiled_ts_multiply`: executable Lean function combinators with no source-AST
  dispatch in their execution.
- `compilation_checked`: the printed function equals the code produced by the
  proof-carrying compiler for this program and entry point.
- `compiled_correct`: equality with the source evaluator for every fuel and list
  of input values. This includes timeout and completed runtime faults.
- `compiled_source`: transfer of a successful compiled execution to `SourceReturns`.

## Supported fragment

The selected function accepts and returns scalar types: `number`, `bigint`,
`boolean`, `string`, `undefined`, `null`, `void`, and supported scalar unions and
aliases. It can use literals, local reads and assignments, unary/binary operators,
short circuiting, conditional expressions, string indexing and `.length`, blocks,
`if`, `while`, `for`, `break`, `continue`, and `return`.

Function/method calls, callbacks, reference parameters/results, reference writes,
and array/record/Map allocation are not compiled yet. This includes scalar builtin
calls such as `Math.abs`. Other functions in the file may use these constructs;
only the selected entry point must fit the compiler fragment. The whole file still
passes the ordinary frontend first.

Unsupported compilation reports `A4101` at the relevant source span, with advice
to use `translate`/`certify` for the larger operational subset. `A4102` reports the
compiler's 256-level nesting budget; `A4103` reports an unknown entry point.
`--json` uses the existing structured diagnostic schema. Compilation errors are
reported before replacing an output file. A failed kernel check leaves a candidate
on disk and reports `A4001`; it does not report certification.

## Proof architecture

`Compile.Fragment α meaning` contains a Lean value `code : α` together with a proof
`code = meaning`. Every compiler constructor supplies that proof. Expressions and
statements preserve their full stateful semantics. The loop combinator has an
inductive preservation theorem, including guard effects, returns, breaks, and
for-loop updates after continue. The entry wrapper also preserves call-frame fuel,
parameter initialization, and scope restoration.

The total compiler returns a `Checked` proof-carrying fragment or a diagnostic.
`Compile.function_correct` extracts the equality from any successful compilation.
It is a general theorem; it does not rely on testing a finite set of inputs, nor on
a universal type-checker soundness theorem.

The fragment's text field is untrusted. Generated `compilation_checked` equations
compare the printed function with the computed fragment's code in the Lean kernel.
A changed source, AST, or target term cannot inherit the original proof silently.
Proof fields are erased during native execution; no external runtime library is
introduced.

## Working with compiled proofs

`Examples/Proofs/Compiled.lean` defines the heap-free specification
`multiply value count = value * max count 0`. It proves that the TypeScript loop
terminates at fuel `count.toNat + 16`, that every larger budget returns the same
value, and that every successful source observation has that result. Negative
counts perform zero iterations. This is an arbitrary-input theorem.

`Examples/Proofs/ScalarExecutions.lean` contains concrete source-linked theorems for
ten compiled programs. Native differential tests additionally cover signed zeros,
NaN, infinities, subnormals, negative bigint division, optional strings, lone
surrogates, early returns, break, and continue. Concrete tests and theorems do not
claim universal correctness for those other algorithms.

## Remaining work

This is a first shallow backend, with explicit dynamic values and heap cells.
It does not yet produce specialized typed state tuples, infer invariants or
termination measures, or compile calls and collections. The binary64 and UTF-16
models remain unchanged. There is no claimed execution speedup over the interpreter
or native TypeScript.

The next compiler extensions should prove named-call/recursion preservation and
then a relation between cells and typed state tuples. Verification-condition
generation can build on those results. The independent grammar, ownership-soundness,
and ECMAScript conformance proofs remain separate obligations.

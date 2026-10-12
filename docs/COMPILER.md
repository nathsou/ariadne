# Verified scalar compiler

`compile` selects one function from an accepted TypeScript file and emits a Lean
function assembled from `Target` combinators. It checks the artifact with the Lean
kernel before reporting success:

```sh
.lake/build/bin/ariadne compile examples/recursive/countdown.ts countdown \
  --out work/Countdown.lean --namespace Countdown
```

The output retains the source certificate and operational wrapper, and adds:

- `compiled_ts_countdown`: executable Lean function combinators. Named calls use
  a compiled definition table; scalar/string builtins execute directly.
- `compilation_checked`: the printed function equals the code produced by the
  proof-carrying compiler for this program and entry point.
- `compiled_correct`: equality with the source evaluator for every fuel and list
  of input values. This includes timeout and completed runtime faults.
- `compiled_source`: transfer of a successful compiled execution to `SourceReturns`.

Linked artifacts also expose `compiled_definitions`, checked through the entry
certificate. The runtime retains an explicit model-compatibility branch for
reference-valued callables; see the boundary below.

## Supported fragment

Compiled functions accept and return scalar types: `number`, `bigint`, `boolean`,
`string`, `undefined`, `null`, `void`, and supported scalar unions and aliases.
They can use literals, local reads and assignments, unary/binary operators, short
circuiting, conditional expressions, string indexing and `.length`, blocks, `if`,
`while`, `for`, `break`, `continue`, and `return`. Calls support forward references,
direct and mutual recursion, nested arguments, scalar builtins such as `Math.sqrt`
and `BigInt`, and the supported string methods.

Callbacks, reference parameters/results, reference writes, and array/record/Map
allocation are not compiled yet. A linked compilation unit requires **every
function in that file** to fit the scalar backend, including unused functions.
Reachability pruning is future work. Call-free entries retain single-function
compilation, so unrelated functions may use the larger operational subset.
The whole file passes the ordinary frontend before either path is selected.

Unsupported compilation reports `A4101` at the relevant source span, with advice
to use `translate`/`certify` for the larger operational subset. Linked-unit errors
also identify the function being compiled and explain the whole-unit restriction.
`A4102` reports the compiler's 256-level nesting budget; `A4103` reports an unknown
entry point. `--json` uses the existing structured diagnostic schema. Compilation
errors are reported before replacing an output file. A failed kernel check leaves
a candidate on disk and reports `A4001`; it does not report certification.

## Proof architecture

`Compile.Fragment α meaning` contains a Lean value `code : α` with a proof
`code = meaning`. Expressions and statements preserve their full stateful
semantics. The loop proof includes guard effects, returns, breaks, and for-loop
updates after continue. The entry wrapper preserves parameter initialization,
call-frame fuel, and caller-environment restoration.

`Compile.Open.Fragment` additionally abstracts the call runtime and proves
**causality**: runtimes agreeing through a fuel budget produce code agreeing
through that budget. `Calls.lean` proves this property for each target combinator.
`Compile.TableFor` binds names, parameters, and compiled bodies to the source
function table. `Compile.link_correct` uses these certificates and induction on
link depth to prove agreement with the source runtime at every covered budget.
Choosing link depth equal to runtime fuel suffices, even for mutual recursion.
This preserves the exact source budget; a callee does not reset it.

The total compiler returns a `Checked` proof-carrying fragment or a diagnostic.
`Compile.entry_correct` extracts equality from successful compilation. This is a
general theorem, independent of finite testing or checker-soundness assumptions.
It covers arbitrary input value lists, not just well-typed scalar arguments.

That last guarantee explains a deliberate boundary: `Target.link` directly handles
named functions and string methods, but delegates other callable values to an
explicit `external` handler, instantiated with the source runtime in emitted code.
Scalar compilation cannot allocate closures or collections. Nevertheless, proving
that no execution can reach the compatibility branch requires a heap-shape
invariant, which is not yet available. Do not describe the entire linked target as
independent of the operational model. The universal countdown proof allows any
external handler, establishing that this particular program never needs it.

The fragment's text field is untrusted. Generated `compilation_checked` equations
compare printed code with the computed fragment's code in the Lean kernel.
A changed source, AST, target term, or linked table cannot inherit the original
proof silently. Proof fields are erased during native execution; no external
runtime library is introduced.

## Working with compiled proofs

`Examples/Proofs/Compiled.lean` proves the loop specification
`multiply value count = value * max count 0` for arbitrary integers. It establishes
termination at fuel `count.toNat + 16`, stability at every larger budget, and
uniqueness of successful source observations.

`Examples/Proofs/Recursion.lean` proves `countdown count = max count 0` for arbitrary
integers at fuel `8 * count.toNat + 12`, with the same stability and uniqueness
results. Its stronger internal statement permits any starting heap and external
handler and proves restoration of the caller's environment.

`Examples/Proofs/Divergence.lean` proves that `forever` times out at every budget
and has no completed outcome in the approximation-based convergence model.
It makes no claim about a native JavaScript engine's stack limit.

`ScalarExecutions.lean` and `RecursiveExecutions.lean` contain concrete source-linked
regression theorems. Recursive examples include parity, Fibonacci, bounded Collatz,
Ackermann, local frame restoration, short circuiting, argument fault order, and
builtin composition. Native tests cover these alongside scalar edge cases; they
also compare exact model/compiled observations at small budgets, substitute a
failing external handler, and check rejection of a tampered linked table.

## Remaining work

The target still uses dynamic values and explicit local cells. Next prove a
heap-shape invariant to remove the reference-call compatibility branch, then a
relation between cells and typed state tuples. Verification-condition generation,
collection compilation, and automated termination proofs follow those foundations.
Reachability pruning can reduce the whole-unit restriction independently.

The binary64/UTF-16 models and native realm contract remain unchanged. There is no
claimed speedup over native TypeScript. Independent grammar, ownership-soundness,
and ECMAScript conformance proofs remain separate obligations.

# Ariadne

A dependency-free Lean 4 frontend, scalar compiler, and executable-model translator
for a restricted TypeScript dialect.

**Ariadne v2** (`V2/`, the `ariadne2` tool) is the current approach: one general correctness
theorem, proved once, instead of per-program certificates. It is described [below](#ariadne-v2) and in
[the v2 design](docs/V2-DESIGN.md) and [progress](docs/V2-PROGRESS.md). The rest of this page
describes v1. The lexer, parser, checker, heap model, command-line
tool, and proof library are written in Lean. Native JavaScript is used only by tests
and the optional host bootstrap.

**Status:** experimental, with a verified scalar compiler and a larger source-bound
operational translation. The frontend accepts functions, local mutation, `while`/`for`, native dense arrays and Maps, typed callbacks,
`number`, `bigint`, UTF-16 strings, booleans, optional values, records, and tuples.
`compile` emits proved-correct Lean function combinators for a smaller scalar
fragment; `translate`/`certify` emit the larger operational model. The compiler still
uses explicit cells and fuel. Read [the proof boundary](docs/TRUST.md) before using
its theorems as claims about a deployed JavaScript program.

## Build and use

The repository pins Lean 4.35.0 (`lean-toolchain`); CI downloads it and Bun 1.4.3 with
reviewed SHA-256 hashes (`scripts/install-ci-tools.sh`). There are no Lake or npm dependencies.

```sh
lake build ariadne
.lake/build/bin/ariadne check examples/fibonacci.ts
.lake/build/bin/ariadne check examples/negative/alias.ts --json
.lake/build/bin/ariadne eval examples/fibonacci.ts demo
.lake/build/bin/ariadne certify examples/fibonacci.ts \
  --out work/Fibonacci.lean --namespace Fibonacci
.lake/build/bin/ariadne compile examples/scalar/multiply.ts multiply \
  --out work/Multiply.lean --namespace Multiply
.lake/build/bin/ariadne extract examples/shallow/scalars.ts \
  --out work/Shallow.lean --namespace Shallow
```

Run commands from this repository's root. `compile` and `certify` need `lake` on
`PATH` and invoke `lake env lean` to check its output. `translate` only writes an **uncertified candidate**;
`check` only accepts or rejects the subset. Neither silently claims certification.
The original TypeScript can run directly in a conforming controlled JavaScript realm.

For all checks, install Bun (CI pins 1.4.3), or use Node 24+:

```sh
scripts/check.sh
```

The script builds certificates serially to bound peak memory, checks generated files
against their sources, audits theorem dependencies, and runs native comparisons.
No JavaScript engine is needed to build the translator or check Lean proofs.

The `extract` backend also writes a sibling `.runtime.ts` module. Its exported
entry wrappers reject overlapping borrowed arguments before mutation. The Lean
artifact kernel-checks the wrapper bytes and type-directed guard plans; use the
runtime module when calling translated exports from a host program. Heap shape,
encapsulation and pristine-realm assumptions remain in [the runtime contract](docs/RUNTIME.md).

The initial `extract` backend emits native Lean definitions with
kernel-checked Core elaboration and denotation equations. It supports branches,
local reassignment, binary64 arithmetic, bigint arithmetic without division,
UTF-16 strings, options, readonly array operations, indexed pure callbacks,
array/Map/Set iteration, locally owned collection updates, counted bigint loops,
scalar switches, and calls with scalar or immutable parameters. It also extracts
named records, tagged unions, borrowed state, classes and Int53 arithmetic. All
three reference programs extract and have universal native proofs, and those
proofs are transferred to the TypeScript source: each reference program is
proved for all inputs against the original evaluator. Generated
source-transfer theorems currently cover supported scalar expressions, local
bindings, scalar reassignment, conditional early returns and guarded Int53
arithmetic, comparisons and unary Math calls, plus array functions built from
`filter`/`map`/`reduce`/`some`/`every`/`find` over scalar arrays and functions
that build or read records of scalars. General data/state/class adequacy
for other programs and the M5 extensions remain in progress. See
[milestone status](docs/SHALLOW-PROGRESS.md).

## What is proved

Each generated module embeds the exact source, characters, tokens, and AST. Its kernel-checked
lexer, parser, and checker equations establish that these artifacts belong together.
Transfer theorems connect properties of its operational model to that source text.
The printer and native translator executable are outside this correctness chain.

The scalar compiler carries semantic equality proofs for every successful result.
Its emitted function is kernel-checked against that compiler result. The
[compiled multiplication proof](Examples/Proofs/Compiled.lean) covers arbitrary
integers, an explicit termination bound, and every larger fuel budget.

The proof library also proves fuel stability and deterministic completed outcomes
for the full evaluator, a general loop-invariant rule, Map lookup/update laws,
and conditional equivalences from modeled `Array.map`/`reduce` to Lean
`List.map`/`foldl`. The [arithmetic examples](Examples/Proofs/Arithmetic.lean) prove
absolute value, maximum, and clamp properties for arbitrary integers. The
[execution examples](Examples/Proofs/Executions.lean) prove concrete terminating runs
of Fibonacci, Euclid, exponentiation, binary search, insertion sort, histograms,
callbacks, and Unicode operations, including final collection contents.

This does **not** prove that the handwritten grammar is the ECMAScript specification,
that the checker is sound for all accepted programs, or that a JavaScript engine
implements the model. Fuel exhaustion is inconclusive. Dynamic array bounds and
incoming heap/realm assumptions remain explicit obligations.

## Ariadne v2

v2 translates a TypeScript file into Lean and proves, once for every program, that running
the source in a reference model of JavaScript gives what the readable Lean definitions say
(`V2.adequacy`). Each translated file carries, per function, a theorem `«f».source` stating
this for the actual source text, checked by Lean's kernel. Properties proved about the
readable definitions therefore hold of the TypeScript functions on every input that meets the
function's safety condition (integer arithmetic stays within the safe-integer range;
comparators are consistent).

It covers booleans, `bigint`, strings, integer-valued `number`, records, unions and optionals,
arrays with their usual methods and callbacks, `let` and loops, `switch`, and classes whose state
is private `Map` fields. drive's kernel files `trust.ts`, `registers.ts` and `tree.ts` translate,
with properties proved in `V2Tests/*Spec.lean`.

```sh
lake build ariadne2
.lake/build/bin/ariadne2 translate file.ts --out Out.lean --namespace Out
lake env lean Out.lean                # kernel-checks the translation and its theorems
.lake/build/bin/ariadne2 run file.ts f 3n '"text"' true
scripts/v2-check.sh                   # everything CI runs for v2
```

What is trusted: Lean's kernel, the model of JavaScript (`V2/Model`, tested against Bun on
41,700 calls), and the parser and converter that turn the file into the model's syntax. See
[the trusted base](docs/V2-PROGRESS.md#trusted-base-l0).

## Documentation

- [Ariadne v2: design](docs/V2-DESIGN.md) and [progress](docs/V2-PROGRESS.md)

- [Language and supported operations](docs/LANGUAGE.md)
- [Scalar compiler and proof workflow](docs/COMPILER.md)
- [Native runtime and ownership contract](docs/RUNTIME.md)
- [Proof coverage and trusted boundary](docs/TRUST.md)
- [Diagnostics and editor payloads](docs/DIAGNOSTICS.md)
- [Architecture and development](docs/ARCHITECTURE.md)
- [Performance consequences](docs/PERFORMANCE.md)
- [Implementation stages and remaining research](docs/IMPLEMENTATION.md)
- [Design proposal: certified shallow translation](docs/DESIGN.md)

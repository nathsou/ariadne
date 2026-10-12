# Ariadne

A dependency-free Lean 4 frontend, scalar compiler, and executable-model translator
for a restricted TypeScript dialect. The lexer, parser, checker, heap model, command-line
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

Install [elan](https://github.com/leanprover/elan); the repository pins Lean 4.34.1.
There are no Lake or npm dependencies.

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

For all checks, install Bun (CI pins 1.3.5), or use Node 24+:

```sh
scripts/check.sh
```

The script builds certificates serially to bound peak memory, checks generated files
against their sources, audits theorem dependencies, and runs native comparisons.
No JavaScript engine is needed to build the translator or check Lean proofs.

The initial `extract` backend emits native Lean definitions with
kernel-checked Core elaboration and denotation equations. It supports branches,
local reassignment, binary64 arithmetic, bigint arithmetic without division,
UTF-16 strings, options, readonly array operations, indexed pure callbacks,
array iteration, counted bigint loops, scalar switches, and calls with scalar
or immutable parameters. It does not yet prove operational adequacy or extract
the three reference programs. See [milestone status](docs/SHALLOW-PROGRESS.md).

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

## Documentation

- [Language and supported operations](docs/LANGUAGE.md)
- [Scalar compiler and proof workflow](docs/COMPILER.md)
- [Native runtime and ownership contract](docs/RUNTIME.md)
- [Proof coverage and trusted boundary](docs/TRUST.md)
- [Diagnostics and editor payloads](docs/DIAGNOSTICS.md)
- [Architecture and development](docs/ARCHITECTURE.md)
- [Performance consequences](docs/PERFORMANCE.md)
- [Implementation stages and remaining research](docs/IMPLEMENTATION.md)
- [Design proposal: certified shallow translation](docs/DESIGN.md)

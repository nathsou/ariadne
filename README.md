# Ariadne

A dependency-free Lean 4 frontend and certifying executable-model translator for a
restricted TypeScript dialect. The lexer, parser, checker, heap model, command-line
tool, and proof library are written in Lean. Native JavaScript is used only by tests
and the optional host bootstrap.

**Status:** an experimental, source-bound operational translation. It accepts
functions, local mutation, `while`/`for`, native dense arrays and Maps, typed callbacks,
`number`, `bigint`, UTF-16 strings, booleans, optional values, records, and tuples.
It generates a deeply embedded, fuel-indexed Lean model, not an optimized Aeneas-style
shallow functional translation. Read [the proof boundary](docs/TRUST.md) before using
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
```

Run commands from this repository's root. `certify` needs `lake` on `PATH` and invokes
`lake env lean` to check its output. `translate` only writes an **uncertified candidate**;
`check` only accepts or rejects the subset. Neither silently claims certification.
The original TypeScript can run directly in a conforming controlled JavaScript realm.

For all checks, install Bun (CI pins 1.3.5), or use Node 24+:

```sh
scripts/check.sh
```

The script builds certificates serially to bound peak memory, checks generated files
against their sources, audits theorem dependencies, and runs native comparisons.
No JavaScript engine is needed to build the translator or check Lean proofs.

## What is proved

Each generated module embeds the exact source, characters, tokens, and AST. Its kernel-checked
lexer, parser, and checker equations establish that these artifacts belong together.
Transfer theorems connect properties of its operational model to that source text.
The printer and native translator executable are outside this correctness chain.

The proof library includes a general loop-invariant rule, Map lookup/update laws,
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
- [Native runtime and ownership contract](docs/RUNTIME.md)
- [Proof coverage and trusted boundary](docs/TRUST.md)
- [Diagnostics and editor payloads](docs/DIAGNOSTICS.md)
- [Architecture and development](docs/ARCHITECTURE.md)
- [Performance consequences](docs/PERFORMANCE.md)
- [Implementation stages and remaining research](docs/IMPLEMENTATION.md)

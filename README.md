# Ariadne

Ariadne translates a subset of TypeScript into readable Lean 4 definitions, together with
**one correctness theorem, proved once in Lean**: for every program it accepts, running the
TypeScript (in a small, executable model of JavaScript) gives exactly what the generated
definitions compute. Properties proved about the definitions therefore hold of the TypeScript
code, with no proof work per program.

Each translated file carries, for every function `f`, a kernel-checked theorem `f.source`
about the source text itself: on any JavaScript arguments representing its inputs, and when
`f`'s safety condition holds (integer arithmetic stays within ±(2^53 − 1); sort comparators are
consistent), every run of `f` converges to a value representing the readable definition's
result.

The motivating user is the verified kernel of [nathsou/drive](https://github.com/nathsou/drive):
its `trust.ts`, `registers.ts` and `tree.ts` translate (the last two unchanged), and their main
properties are proved in `Tests/*Spec.lean`.

## Build and use

The repository pins Lean 4.35.0 (`lean-toolchain`) and has no Lake dependencies; its one npm
dependency, the TypeScript compiler, is test-only (the parser cross-check) and pinned by `bun.lock`. CI
downloads Lean and Bun 1.4.3 with reviewed SHA-256 hashes (`scripts/install-ci-tools.sh`).

```sh
lake build ariadne
.lake/build/bin/ariadne translate file.ts --out Out.lean --namespace Out
lake env lean Out.lean      # kernel-checks the translation and its theorems
scripts/check.sh            # everything CI runs (needs Bun, or Node 24+)
```

`translate` writes the source's syntax tree, its typed version, readable definitions, safety
conditions and one source theorem per function. `ariadne batch FILE` evaluates calls in the
model (a test oracle), and `ariadne signatures FILE` prints the exported signatures.

## What is proved, and what is trusted

`Ariadne.adequacy` (`Ariadne/Proof/Adequacy.lean`) is proved by induction on typed syntax, once
for every program. Per file, the kernel only checks structural equations: that the typed program
erases to the parsed one, that it is well formed, and that the printed definitions are its
denotation.

`lake exe audit` is the soundness gate:
- every declaration re-checks with Lean's kernel;
- every theorem uses only `propext`, `Classical.choice` and `Quot.sound` (no `sorry`);
- nothing a theorem depends on is `partial`, `unsafe`, `implemented_by` or `extern`;
- the trusted base is exactly what `trusted.lock` records: the model, the relations the theorems state
  results in, and the theorems' statements. A change to any of it is a change to that file, to review.

Trusted:

- Lean's kernel;
- the model of JavaScript (`Ariadne/Model`), tested against Bun on 41,700 calls
  (`scripts/differential.mjs`) and on hand-written cases (`scripts/model.mjs`);
- the parser and the converter to the model's syntax (`Ariadne/Parse`, `Ariadne/Front/Convert.lean`).

The type checker, the printer and every tactic are untrusted: a bug in any of them makes a
per-file check fail, never a wrong theorem.

Each source theorem assumes that its arguments represent the declared types (safe integers, records with
their fields, arrays without holes). `ariadne validators FILE` prints TypeScript guards that check it
where values enter from outside the subset.

## Using Ariadne in a project

Require it in the project's `lakefile.toml`, pinned to a release:

```toml
[[require]]
name = "ariadne"
git = "https://github.com/nathsou/ariadne"
rev = "v0.4.0"
```

[docs/GUIDE.md](docs/GUIDE.md) walks through a whole project, [`examples/quickstart`](examples/quickstart),
which CI builds and audits: translating, stating and proving claims, the audit, and CI with a prebuilt
release (`scripts/fetch-release.sh`, its hash pinned). [CHANGELOG.md](CHANGELOG.md) lists what each
release changes.

Translate each TypeScript file with `lake exe ariadne translate`, check the generated files in, and
prove properties of the readable definitions (`Ariadne/Lib` has lemmas for their loops, maps, string
order and sorting; `cmp_laws` proves a comparator lawful, which `toSorted`'s safety condition needs; a
class's file states which fields each method leaves alone, as `m.keeps.f`). `Ariadne.Audit.run` gives the project the same soundness
gate, with its own lock: for example, every proposition defined under `Spec` must be proved exactly by
the theorem of the same name under `Proofs`, and the lock records every statement, so a changed
statement is a visible change in review.

## Documentation

- [Playground: translate TypeScript in the browser, and step through proofs](https://nathsou.github.io/ariadne/)
  ([source](playground/README.md))
- [Guide: a project from TypeScript to proved properties](docs/GUIDE.md)
- [Design: the model, the typed syntax, the theorem and the per-file checks](docs/DESIGN.md)
- [Language: what is accepted, what is refused, and drive's kernel](docs/LANGUAGE.md)

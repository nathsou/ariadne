# Ariadne

Ariadne translates a subset of TypeScript into readable Lean 4 definitions, together with
**one correctness theorem, proved once in Lean**: for every program it accepts, running the
TypeScript (in a small, executable model of JavaScript) gives exactly what the generated
definitions compute. Properties proved about the definitions therefore hold of the TypeScript
code, with no proof work per program.

Each translated file carries, for every function `f`, a kernel-checked theorem `«f».source`
about the source text itself: on any JavaScript arguments representing its inputs, and when
`f`'s safety condition holds (integer arithmetic stays within ±(2^53 − 1); sort comparators are
consistent), every run of `f` converges to a value representing the readable definition's
result.

The motivating user is the verified kernel of [nathsou/drive](https://github.com/nathsou/drive):
its `trust.ts`, `registers.ts` and `tree.ts` translate (the last two unchanged), and their main
properties are proved in `Tests/*Spec.lean`.

## Build and use

The repository pins Lean 4.35.0 (`lean-toolchain`) and has no Lake or npm dependencies. CI
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
denotation. No `sorry`, and only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), checked for every theorem by `scripts/Audit.lean`.

Trusted:

- Lean's kernel;
- the model of JavaScript (`Ariadne/Model`), tested against Bun on 41,700 calls
  (`scripts/differential.mjs`) and on hand-written cases (`scripts/model.mjs`);
- the parser and the converter to the model's syntax (`Ariadne/Parse`, `Ariadne/Front/Convert.lean`).

The type checker, the printer and every tactic are untrusted: a bug in any of them makes a
per-file check fail, never a wrong theorem.

## Documentation

- [Design: the model, the typed syntax, the theorem and the per-file checks](docs/DESIGN.md)
- [Language: what is accepted, what is refused, and drive's kernel](docs/LANGUAGE.md)

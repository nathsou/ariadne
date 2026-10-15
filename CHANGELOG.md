# Changelog

Ariadne follows semantic versioning: a minor version may change generated files and the trusted base
(`trusted.lock` shows how); a patch version changes neither. Projects pin a release tag (see
[docs/GUIDE.md](docs/GUIDE.md)).

## Unreleased

**Language**
- `x++` and `x--` on bigints. Increments are model operators (`inc`, `dec`) rather than `x = x + 1`,
  which a bigint could not be written as.

**Command line**
- `ariadne validators FILE [--out FILE.ts]`: a TypeScript module with a guard per exported function and
  method, `args.f(...)`, true only if the arguments represent `f`'s parameter types, as its source theorem
  assumes. For callers at a boundary (storage, the network). Tested by `scripts/validators.mjs`.

**Proof library**
- `ariadne_safe [facts]`: proves a safety condition that holds on every input given the facts.

**Trusted base**
- `trusted.lock`: `UnOp.inc`, `UnOp.dec` and their evaluation.

**Playground**
- [playground/](playground/README.md): a static page (GitHub Pages) where the translator, compiled to
  WebAssembly, runs in the browser as one types. It shows the readable definitions and live type hovers,
  explains refusals with suggested rewrites, runs calls in the model and as JavaScript side by side, and
  steps through kernel-checked proofs of its examples (with goal states recorded in CI).
- The checker logs what each checked expression, variable and function denotes (`translateLogged`); the
  generated files are unchanged. The parser imports `Lean.Data.Json` instead of all of `Lean`.

**Checks**
- `scripts/differential.mjs` takes a directory of compiled modules: JavaScript then runs the file as a
  production build emits it (bundled, minified) while the model runs the source. CI runs the fixtures both
  ways.

## v0.4.0

**Language**
- `while (c) { … }` with a condition free of number arithmetic. Its safety condition says the loop ends
  within 2^64 iterations; prove it with a measure (`whileSafe_of_measure`).
- `%` on numbers and bigints, `/` on bigints, and `Math.floor(a / b)` on numbers (exact floor division
  on safe integers). Declarations named `Math` are refused.
- On strings: `startsWith`, `endsWith`, `includes`, `indexOf`, and `slice` with one or two arguments.

**Generated files**
- Readable names: aliases written as the Lean types they denote; accessors, constructors and setters for
  records; constants for literal unions; constructors (usable as patterns) for unions of records. Readable
  definitions use them, and take loop and join-point states apart by pattern.
- A class's file states which fields each method leaves alone: `«m».keeps.«f» : (m this …).f = this.f`,
  from one general theorem (`TProgram.frame`).

**Proof library** (`Ariadne/Lib`)
- `cmp_laws`: proves a comparator lawful (so `toSorted`'s safety condition holds) when it is a chain of
  keys, as comparators usually are.
- Loops: `forIn_continue` (a loop that never leaves early is a fold), `whileDo_inv`,
  `whileSafe_of_measure`.
- Maps (`mapGet` after `mapPut`/`mapDel`, keys and their distinctness), string order (`strLt` is a
  strict total order), `toSorted` (what it returns).

**Trusted base and checks**
- `trusted.lock` records the model's new operators, string methods and `while`.
- The parser and converter are cross-checked against the TypeScript compiler (`scripts/crosscheck.mjs`),
  and the model against Bun on random programs (`scripts/fuzz-model.mjs`).
- `ariadne ast FILE` prints the converted program.
- `Ariadne.Audit.Config.replay`: replays a dependency's declarations without locking them, so a prebuilt
  Ariadne needs no trust.

**Releases**
- Tagged releases publish the build and its SHA-256 (`scripts/fetch-release.sh`).
- `examples/quickstart`: a project depending on Ariadne, built and audited in CI.

## v0.3.0

The first version used by drive: the model, typed syntax, denotation and adequacy theorem; classes with
`Map` fields; the audit and `trusted.lock`.

# Changelog

Ariadne follows semantic versioning: a minor version may change generated files and the trusted base
(`trusted.lock` shows how); a patch version changes neither. Projects pin a release tag (see
[docs/GUIDE.md](docs/GUIDE.md)).

## Unreleased

**Model and certificate layout**
- `translate --split` emits a readable `Model.lean`, a `Certificate.lean`, and an umbrella
  importing both. Existing function and theorem names stay the same; the standalone format remains.
- Checking, structured code emission and file assembly have separate frontend modules.
  Loop declarations no longer travel through marker strings; variable/type dependencies are collected
  structurally. Identity bindings disappear and certificate proofs share named prefixes.
- Every nontrivial safety condition has a checked `f.safe_iff`, a simplified proposition for proofs.
  The raw condition still participates in the structural correctness check.
- `whileDo_measure` is available in `Ariadne.Lib.Loop`. Canonical and named denotations share the
  `Control` continuation representation; the staged equivalence proofs remain.
- CI regenerates both layouts and playground examples, checks mutation rejection, and builds the
  playground proof examples. The playground shows the model of large split examples.

**Readable definitions**
- Names print bare unless Lean needs guillemets (keywords such as `at`, `this`; names that are not
  identifiers). List operations on a name or field path use dot notation (`xs.length`, `xs.map f`).
- The source's types are Lean declarations: a record is a `structure` (read by name, built with `mk`,
  updated with `{ r with f := v }`), a union of records an `inductive` with a constructor per variant
  (`Entry.credit amount`; a variant with more fields takes a structure), and a variant record is its
  payload. A record or union whose names Lean cannot use for a structure's fields or an inductive's
  constructors stays a product or a sum. Proofs use `cases`, `rcases` and field names instead of tuple
  positions.
- A loop whose body has no `return` and no `break` of its own reads as a fold, its body a named
  definition taking the variables it reads, its state the variables it assigns:
  ```lean
  def sum.loop : Int → Int → Int :=
    fun total x =>
      let total : Int := total + x
      total

  def sum (xs : List Int) : Int :=
    let total : Int := (0 : Int)
    let total := Ariadne.fold total xs sum.loop
    total
  ```
  Other loops are `forIn` with `next`/`exit` continuations, their bodies named too, their state also the
  assigned variables; an `if` or `switch` whose branches all go on gives those variables as its value
  (`let (neg, pos) := if … then … else …`).
- How it stays proven: the readable definitions are checked by `rfl` against `TStmts.denoteRS`
  (`Ariadne/Typed/Named.lean`), a denotation over the file's structures and inductives (`names`, `isos`,
  generated with the file), with loops as folds and states of assigned variables. It is proven equal to
  `denote` once, for every program, in three steps (`TStmts.denoteFn_eq`, `denoteFn_eq_R`,
  `denoteFn_eq_S` in `Ariadne/Proof/{Direct,Idiom,Named}.lean`). The general theorem and `trusted.lock`
  are unchanged. Source theorems state representation over the file's types (`ArgsRepS`, `Ty.RepS`, equal
  to `ArgsRep` and `Ty.Rep` after `Ty.conv`, and unfolding to them on types without structures or
  inductives). Generated files, and proofs about records, unions and loops, change (a minor version).
- Frame lemmas name the method and the field's accessor (`frame_of_fnS`), so checking them never unfolds
  a readable body.
- Safety conditions (`f.safe`) carry the same states as the definitions: a loop's state is the variables
  it assigns, not the whole environment, and branches that go on join through `let after := fun state =>
  …`, used only when what follows reads a variable the branches narrowed. A loop invariant proven for a
  definition applies to its safety condition as it is. Checked against `TStmts.safeS`, a copy of
  `TStmts.safeR` (`Ariadne/Typed/Idiom.lean`), proven equal to `safe` once (`TStmts.safeFn_eq_R`).
  Proofs that destructured the environment in a safety condition's loop take the state instead.

**Proof library**
- `fold_inv`: an invariant of `Ariadne.fold`, with each item's membership in the list.
- `fold_prefix`: an invariant of `Ariadne.fold` over the items seen so far (`P pre s`), each step given
  where its item sits (`items = pre ++ y :: post`); `fold_eq`: a fold equals `g items` when each step
  extends `g` by one item.
- `ariadne_safe [facts]`: proves a safety condition that holds on every input given the facts.

**Language**
- `x++` and `x--` on bigints. Increments are model operators (`inc`, `dec`) rather than `x = x + 1`,
  which a bigint could not be written as.

**Command line**
- `ariadne validators FILE [--out FILE.ts]`: a TypeScript module with a guard per exported function and
  method, `args.f(...)`, true only if the arguments represent `f`'s parameter types, as its source theorem
  assumes. For callers at a boundary (storage, the network). Tested by `scripts/validators.mjs`.

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

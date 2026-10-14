# Guide: from TypeScript to proved properties

This walks through [`examples/quickstart`](../examples/quickstart), a project that depends on Ariadne. CI
builds and audits it, so every step here works as written.

## 1. Set up the project

A Lean project with the same toolchain as Ariadne (`lean-toolchain`), requiring a release:

```toml
# lakefile.toml
name = "quickstart"
defaultTargets = ["Quickstart"]

[[require]]
name = "ariadne"
git = "https://github.com/nathsou/ariadne"
rev = "v0.4.0"

[[lean_lib]]
name = "Quickstart"

[[lean_exe]]
name = "audit"
root = "Audit"
supportInterpreter = true
```

(The example requires Ariadne by path instead, to test the current commit.) `lake update` fetches it;
`lake exe ariadne` builds the translator on first use, or `scripts/fetch-release.sh` downloads the
release's build (see 6).

## 2. Translate

Write the code in the subset ([LANGUAGE.md](LANGUAGE.md)), then:

```sh
lake exe ariadne translate src/ledger.ts --out Quickstart/Ledger.lean --namespace Quickstart.Ledger
```

Check the generated file in; CI regenerates it and fails on a difference. It holds:

- readable definitions: `«balance»`, the class's methods `«credit»`, `«freeze»`, …, and the types'
  names (`«Entry».«credit» amount`, `a.«balances»`, `a.«withBalances» m`);
- `«f».safe`, the condition under which `f` stays within what the model covers, for each function
  that can leave it (number overflow, a zero divisor, an inconsistent comparator, a `while` loop that
  does not end);
- `«f».source`: every run of the TypeScript `f`, on arguments representing the inputs (and with
  `«f».safe` holding), converges to what the readable definition gives;
- for a class, `«m».keeps.«f»`: method `m` leaves the field `f` alone.

## 3. State what you claim

Claims are propositions in a specification namespace (`Quickstart/Spec.lean`), each proved by the theorem
of the same name in a proofs namespace:

```lean
def balance_nonneg : Prop :=
  ∀ entries : List «Entry», (∀ e ∈ entries, 0 ≤ amount e) → 0 ≤ «balance» entries
```

A claim about the definitions holds of every run of the code through `«f».source`; a claim can also state
that directly, as `freeze_runs` does.

## 4. Prove

`Quickstart/Proofs.lean`. What helps:

- **Loops**: `forIn_inv` (an invariant), `forIn_prefix` (an invariant over the items seen so far, as in
  `balance_nonneg`), `forIn_continue` (a loop that never leaves early is a fold); for `while`,
  `whileDo_inv` and, for its safety condition, `whileSafe_of_measure`.
- **Classes**: the generated `«m».keeps.«f»` lemmas, and `Ariadne/Lib/Map.lean` for the maps
  (`mapGet_mapPut`, …).
- **Sorting**: `cmp_laws` proves a comparator lawful; then `consistent_of_laws` discharges `toSorted`'s
  safety condition, and `sortedBy_perm`, `sortedBy_sorted` say what it returns.
- **Names**: `simp [readable]` unfolds the generated names to tuples, when a proof needs to.
- **Safety conditions**: unfold `«f».safe`, split its cases, and close each with what bounds the numbers
  (`inRange`, `omega`).

## 5. Audit

`Audit.lean` runs Ariadne's soundness gate:

```lean
unsafe def main (args : List String) : IO UInt32 :=
  Ariadne.Audit.run {
    modules := #[`Quickstart]
    project := [`Quickstart]
    replay := [`Ariadne]
    lockNamespaces := [`Quickstart.Spec]
    specs := some (`Quickstart.Spec, `Quickstart.Proofs)
    lockPath := "spec.lock"
    lockHeader := "-- spec.lock: … review every change." } args
```

`lake exe audit` fails unless every declaration (the project's, and Ariadne's through `replay`) re-checks
with the kernel, theorems use only the standard axioms, every claim is proved exactly, and `spec.lock`
matches. The lock prints the claims and the definitions they mention, so a changed claim, or a change to
the code it is about, is a visible diff in review; `lake exe audit --write-lock` rewrites it.

## 6. CI

Check, on every change: the translation is up to date, `lake build`, `lake exe audit`. Ariadne's own CI
also runs its fixtures in Bun against the model; a project can do the same with `ariadne batch`
([scripts/differential.mjs](../scripts/differential.mjs) is a template).

Building Ariadne from source takes a few minutes. A release publishes its build with a SHA-256:

```sh
lake update
scripts/fetch-release.sh v0.4.0 <sha256 from the release> .lake/packages/ariadne
lake build
```

With `replay := [`Ariadne]`, the audit re-checks every declaration of the prebuilt library, so the
archive is trusted only for the `ariadne` executable, which the pinned hash ties to the release
workflow's build of the tagged commit.

## 7. Updating Ariadne

Bump the tag (and hash), regenerate the translations, and run the audit. Release notes
([CHANGELOG.md](../CHANGELOG.md)) say what changed; the diffs to review are the generated files, and the
project's lock if a claim mentions changed definitions. Ariadne's own trusted base is `trusted.lock` in its
repository: a release that changes the model shows it there.

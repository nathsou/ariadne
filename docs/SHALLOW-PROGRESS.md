# Shallow translation implementation

The acceptance contract is [DESIGN.md](DESIGN.md). Milestones are complete only
when their exit criteria pass; finite native tests are not universal proofs.

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0 | Complete | Reference sources and historical diagnostics; pinned CI downloads; reserved extraction diagnostics; output preservation tests |
| M1 | In progress | All reference programs check and certify; classes, unions, interfaces, readonly/optional fields, narrowing, loops, switch, spread, Sets, escapes, templates and measure syntax implemented. Remaining builtin coverage is tracked below. |
| M2 | In progress | Typed scalar Core, structural denotation, checked extraction, three-way differential and tamper tests. Named types, collections, loops, calls, Int53 safety and reference extraction remain pending. |
| M3 | Pending | Loop invariant/fold lemmas and scalar native proofs are seeded; the universal proofs of the three emitted references remain pending. |
| M4 | Pending | Fundamental lemma, footprint preservation, adequacy and source transfer |
| M5 | Pending | Measures, larger ownership, polymorphism, exceptions and scalar backend integration |

## Reference specifications

`examples/reference/baseline.json` records diagnostics at the design commit. It is
historical evidence, not an assertion that the programs should remain rejected.
`scripts/reference.mjs` exercises the native specification of each reference.

- Decision equality is structural: candidates with the same version and id are
  the same result value, even if allocated separately.
- Register convergence assumes stamps identify consistent operations. Counters
  are per-replica monotone components merged by maximum. Composite key components
  exclude NUL; arbitrary strings would make the encoding non-injective.
- Tree correctness is an invariant of states reachable from a fresh instance.
  Moving to a descendant detaches the moved node. Lookups, rather than Map
  insertion order, specify observable agreement.

## Validation

M0: `scripts/check.sh` passes, including 1,072 audited theorems, the existing
operational and scalar comparisons, adversarial certificates and diagnostics, and
1,728 native tree traces. Lean 4.34.1 and Node 24.19.0 were used locally.

## Current frontend limits

- Iterators returned by `keys`, `values` and `entries` are consumed immediately by
  spread or `for…of`. They are distinct from arrays; storing a live iterator is
  rejected until the checker tracks its lifetime.
- Template interpolation supports strings, bigint, boolean, null and undefined.
  Binary64-to-decimal conversion is not yet modeled.
- Switch clauses must exit explicitly; grouped labels and implicit fallthrough are rejected.
- `@decreases` is preserved and typechecked, but is not a termination proof on
  the operational path. Tier-1 extraction is still pending.
- The full M1 builtin table (search callbacks, sorting, string search, concat/join,
  and variadic Math functions) remains in progress.
- The type/ownership checker still has no general soundness theorem. M4 must
  establish adequacy before extracted definitions can support source claims.

Frontend checkpoint: the complete `scripts/check.sh` suite passes with 1,217
audited theorems, 42 native entry points, 64 generated programs, 51 scalar
comparisons, 37 negative fixtures, and 21 reference inputs/traces. All three
reference operational certificates build in CI. This is not M2–M5 completion.

## Initial extraction fragment

`extract` now accepts pure scalar functions with local reassignment, branches,
bigint addition/subtraction/multiplication and comparisons, binary64 arithmetic,
UTF-16 string operations, and optional scalar values. Branch continuations are
shared through typed tuple arguments. Function calls, loops, named types,
collections, classes, and Int53 refinement are explicitly refused. This is an
incremental M2 slice, not the M2 reference-program exit gate.

The extraction checkpoint passes the complete `scripts/check.sh` suite: 1,559
audited theorems, 39 negative fixtures, and 38 additional three-way scalar
comparisons. A 20-branch stress case checks continuation sharing and closed
results in the kernel. Each shared continuation has its own denotation lemma;
the function certificate composes these lemmas without expanding all paths.

Generated modules contain an intrinsically typed Core term, an elaboration
equation checked by the kernel, native definitions, and per-function denotation
equations. Extraction checks a temporary candidate before replacing output.
The current denotation remains a trust boundary until M4. The scalar proof
examples prove properties of emitted definitions only and do not claim source
transfer.

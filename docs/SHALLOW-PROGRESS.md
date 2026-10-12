# Shallow translation implementation

The acceptance contract is [DESIGN.md](DESIGN.md). Milestones are complete only
when their exit criteria pass; finite native tests are not universal proofs.

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0 | Complete | Reference sources and historical diagnostics; pinned CI downloads; reserved extraction diagnostics; output preservation tests |
| M1 | In progress | All reference programs check and certify; classes, unions, interfaces, readonly/optional fields, narrowing, loops, switch, spread, Sets, escapes, templates and measure syntax implemented. Remaining builtin coverage is tracked below. |
| M2 | Pending | Typed Core, interpretations, elaboration, denotation, extraction and three-way differential tests |
| M3 | Pending | Prelude lemmas and universal proofs of the emitted references |
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

# Shallow translation implementation

The acceptance contract is [DESIGN.md](DESIGN.md). Milestones are complete only
when their exit criteria pass; finite native tests are not universal proofs.

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0 | Complete | Reference sources and historical diagnostics; pinned CI downloads; reserved extraction diagnostics; output preservation tests |
| M1 | Pending | Frontend, ownership and operational parity for all reference programs |
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

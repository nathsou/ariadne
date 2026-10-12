# Implementation stages

The implemented vertical slice covers a handwritten Lean frontend, a conservative
ownership/type checker, explicit scalar/heap/control semantics, source-bound kernel
certificates, a CLI, diagnostics, native differential tests, CI, and proof examples.
It uses no Lake dependencies or external runtime libraries.

The first release's acceptance gates are:

- Every supported source fixture passes parsing/checking and its generated replay
  equations pass the kernel.
- Negative syntax, type, ownership, realm, and callback-effect cases are rejected
  with stable diagnostic codes.
- Native observations agree with the executable model for repository examples and
  deterministic generated programs, including bigint and number edge cases.
- Arithmetic theorems quantify over arbitrary inputs; concrete algorithm executions
  prove their stated results and collection contents without claiming universality.
- General loop, Map, and list-correspondence lemmas state their premises explicitly.
- Regeneration is deterministic and the transitive axiom audit rejects proof holes
  and native-evaluation axioms.

## Remaining research and larger-subset work

This is a usable experimental foundation, not the completion of a universally
verified Aeneas equivalent. The following are explicitly not implemented:

1. An independent formal grammar and a universal proof that parsing implements it.
2. Type/ownership preservation and progress for all accepted programs, plus a precise
   relation to an independently specified ECMAScript subset.
3. A shallow typed functional compiler with a universal simulation theorem. Current
   output calls the proved-source-bound interpreter. The arbitrary-input arithmetic
   proofs demonstrate how readable functional specifications can be connected today.
4. Interprocedural effect summaries, region-based loans, nested mutable references,
   object keys, ownership transfer, and validated external-heap entry points.
5. Modules/import resolution, generic utilities, discriminated unions, richer callback
   inference, and multi-error parser recovery.
6. Automated verification-condition generation, loop invariants, termination
   certificates, and universal correctness proofs for the larger example algorithms.
7. A formal conformance bridge for native binary64/string/collection builtins and
   a verified JavaScript engine or erasure pipeline.

These should be separate reviewable steps with semantic contracts and regression
fixtures, rather than silently broadening acceptance. The host realm and input
contract remains necessary even with a stronger compiler proof: native prototypes,
proxies, getters, and external aliases are properties of the execution environment.

# Implementation stages

The implemented vertical slice covers a handwritten Lean frontend, a conservative
ownership/type checker, explicit scalar/heap/control semantics, source-bound kernel
certificates, a CLI, diagnostics, native differential tests, CI, and proof examples.
It uses no Lake dependencies or external runtime libraries.

The first release's acceptance gates, retained in CI, are:

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

## Scalar compilation milestone

This milestone adds full-evaluator fuel stability, deterministic convergence,
proof-carrying scalar compilation, kernel-checked target emission, ten compiled
examples, and an arbitrary-input multiplication proof with a termination bound.
See [the compiler guide](COMPILER.md) and [the milestone plan](NEXT-STEPS.md).

## Remaining research and larger-subset work

This is a usable experimental foundation, not the completion of a universally
verified Aeneas equivalent. The following are explicitly not implemented:

1. An independent formal grammar and a universal proof that parsing implements it.
2. Type/ownership preservation and progress for all accepted programs, plus a precise
   relation to an independently specified ECMAScript subset.
3. Extending the proved scalar compiler to named calls/recursion, typed state tuples,
   and collections. The current scalar target uses Lean function combinators and
   explicit cells; the larger operational translation still invokes the interpreter.
4. Interprocedural effect summaries, region-based loans, nested mutable references,
   object keys, ownership transfer, and validated external-heap entry points.
5. Modules/import resolution, generic utilities, discriminated unions, richer callback
   inference, and multi-error parser recovery.
6. Automated verification-condition generation, loop invariants, termination
   certificate synthesis, and universal correctness proofs for the larger example
   algorithms. Multiplication already has a manual arbitrary-input termination proof.
7. A formal conformance bridge for native binary64/string/collection builtins and
   a verified JavaScript engine or erasure pipeline.

These should be separate reviewable steps with semantic contracts and regression
fixtures, rather than silently broadening acceptance. The host realm and input
contract remains necessary even with a stronger compiler proof: native prototypes,
proxies, getters, and external aliases are properties of the execution environment.

# Implementation plan

Ariadne is a dependency-free Lean 4 implementation of a restricted TypeScript
frontend and a certifying translation to Lean. The JavaScript engine and its
native primitives are modeled, not reimplemented or verified at the machine-code
level. The initial realm and incoming values must satisfy the runtime contract.

The development sequence is:

1. Pin Lean; establish source spans, structured diagnostics, and certification.
2. Implement a terminating handwritten lexer/parser and independent static checks.
3. Define scalar, heap, collection, and control-flow semantics.
4. Generate source-bound Lean artifacts and check their correspondence proofs.
5. Add loops, calls, ownership checks, and native collection operations.
6. Add substantial source examples and kernel-checked property proofs.
7. Exercise positive/negative inputs, native differential execution, and CI.

Every feature needs an explicit semantic contract, diagnostics, and tests.
Proof coverage must be reported precisely: parsing an embedded source again is a
per-artifact check, not a universal parser-correctness proof. A proof against the
Lean operational model is not a proof of the JavaScript engine. Termination is
separate from partial correctness, and exhausted evaluation fuel is not a source
exception. No `sorry`, user axioms, or native decision procedures are permitted in
the correctness chain.

The implementation has no Lake dependencies. Native execution in tests may use
Bun, which is a CI tool and is not required by the translator or its proof library.

# Recursive scalar calls milestone

This work is stacked on PR #2 until that PR merges. The acceptance gates are:

1. Add an open call interface and prove finite-fuel causality for every target
   combinator. Prove recursive linking correct for all budgets, values, and states,
   including runtime faults and caller-environment restoration.
2. Extend scalar compilation to calls, forward references, direct/mutual recursion,
   and existing scalar/string builtins. Keep the original call-free output shape.
   Certify printed linked tables against the proof-carrying compiler result.
3. Add recursive and composition examples, an arbitrary-input recursive correctness
   and termination proof, native comparisons, and target-table tampering tests.
4. Document the boundaries, run all existing checks, push milestones, and open a
   stacked PR with passing CI.

A linked compilation unit initially requires all functions in that file to fit the
scalar backend. Call-free compilation retains its previous single-entry behavior.
Errors inside a linked function should identify that function and explain the
whole-unit restriction. Reachability pruning is separate work.

The linker directly dispatches compiled named functions and existing scalar/string
builtins. To retain equality with the model on arbitrary states and callable values,
reference-valued callables retain an explicit model-compatibility branch. The scalar
backend cannot allocate closures or collections. Removing the residual branch needs
a proved heap-shape invariant; this milestone must not conceal it or describe the
entire target as independent of the operational model.

Typed state tuples, automated verification conditions, collection compilation,
ownership soundness, and the independent ECMAScript bridge remain later milestones.

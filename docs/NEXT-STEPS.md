# Verified scalar compilation milestone

This milestone builds on PR #1. It has four acceptance criteria:

1. Prove that every evaluator entry point preserves successful results and
   non-timeout faults as fuel increases. Define convergence without selecting a
   budget and prove eventual stability and determinism, including final heaps.
2. Compile a first scalar fragment to executable Lean function combinators.
   Compilation carries a general semantic preservation proof. Generated text
   must be checked against the compiler result by the Lean kernel.
3. Prove a loop-bearing TypeScript function correct for arbitrary inputs, with
   an explicit termination bound. Test loops, control flow, scalar edge cases,
   diagnostics, and rejection of modified generated code.
4. Keep the dependency-free build, run the complete existing checks, document
   remaining proof boundaries, and open a fresh PR from the merged main branch.

The initial compiler will cover literals, local reads/writes, scalar operators,
conditionals, lexical blocks, while/for, break/continue, and return. Calls and
collection allocation are a later extension; compilation will report them at
source locations. Existing operational translation remains available for the
larger accepted language.

The target initially retains explicit local cells and the binary64/UTF-16 value
model. It removes source-AST dispatch, but does not yet turn local state into
specialized tuples or infer termination measures. Those optimizations need a
separate state-representation correctness proof.

Convergence is defined from the existing evaluator's finite approximations.
An independent operational rule system and an ECMAScript conformance theorem
remain separate work; this milestone must not describe the convergence theorem
as either of those results.

After this milestone: named calls and recursion, typed state tuples, verification
condition generation, ownership soundness, collection compilation, and an
independent grammar/ECMAScript semantics bridge, in that order.

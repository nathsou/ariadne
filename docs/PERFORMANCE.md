# Performance consequences

The accepted TypeScript runs with ordinary native arrays, Maps, arithmetic, and
loops. Ariadne does not insert a runtime interpreter, borrow checker, wrapper on
every access, or conversion to linked lists into that TypeScript. Native Map lookup
therefore retains the engine's implementation characteristics; the Lean model's
association list does not determine the JavaScript program's running time.

Restrictions can still affect an algorithm:

- Borrowed in-place mutation, as in insertion sort, needs no defensive copy.
- Preserving two aliases of an array is forbidden. Reorganizing ownership can avoid
  a copy; explicitly copying with `slice` costs O(n) time and additional memory.
- Flat containers rule out some graph-shaped data. Index-based representations can
  be efficient, but their engineering cost and locality depend on the algorithm.
- Mutation during `map`/`forEach` is rejected. A separate pass or explicit loop may
  change allocation and traversal costs; ordinary fusion and in-place algorithms
  remain possible when their aliasing is explicit.
- `bigint` is exact but is not a drop-in performance replacement for `number`.
  Its cost grows with operand size. Native binary64 numbers are supported directly.
- Pristine-realm hardening runs once at host startup; its interaction with engine
  optimization must be measured on the intended engine/workload.

Lean execution and certification are different workloads. The current model uses
lists for environments, heaps, arrays, and ordered Maps. Allocation and lookup can
be linear; old local cells remain allocated. The handwritten lexer also prioritizes
simple kernel-reducible definitions over throughput. Neither is intended as a fast
replacement for native JavaScript execution.

Kernel computation is currently the largest practical cost. Encoding certificates
avoid a costly decoder reduction: the expanded numeric fixture was checked locally
in about 4.9 seconds with roughly 2.2 GiB peak memory after this change; direct
reduction previously exhausted memory. This is one development-machine observation,
not a portable benchmark or a promise about larger inputs. The check script compiles
certificates serially, and the default `lake build` excludes the heavy example proof
suite. No broad native-program speedup/slowdown percentage is claimed.

The scalar backend now specializes source syntax into proved-correct Lean function
combinators. It retains the list-based cells and dynamic scalar representation, so
removing AST dispatch does not establish an asymptotic or measured speedup. Its
correctness proofs are erased during native execution.

PR #4's CI baseline (#82) took 21m18s. The verified class-state checkpoint
(#128) took 8m54s, retaining all original checks and adding proof witnesses.
Regeneration avoids duplicate shallow checking; source/Int53 tamper tests use
small fixtures; serial certificate/test jobs run on separate runners. A pinned
Actions cache reuses unchanged library modules, with Lake build and regeneration
always run after restoration. The #128 preparation build took 27s after an
incremental restore, compared with 260s in the uncached #124 run. Its source and
Int53 tamper phases took 21s/9s versus 111s/89s in the baseline. Runner variability
and a cold cache affect the wall time; these are observed CI timings.

Logs: [baseline #82](https://github.com/nathsou/ariadne/actions/runs/38294746569)
and [class state #128](https://github.com/nathsou/ariadne/actions/runs/38359764572).

Future work should profile parser sharing, use certificates with smaller replay
steps, and prove a transition from cells to specialized typed state tuples. Measure these separately from native runtime
performance so that a faster checker is not mistaken for a faster TypeScript program.

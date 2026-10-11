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

Kernel computation is currently the largest practical cost: certificates for the
small repository examples take seconds, sometimes tens of seconds, on the development
machine, and parallel certificate builds can consume substantial memory. The check
script compiles them serially. Those observations are not portable benchmarks or a
promise about larger inputs. No broad speedup/slowdown percentage is claimed.

Future work should profile parser sharing, use validated certificates with smaller
replay steps, specialize the operational model into shallow functions, and prove
that optimization preserves behavior. Measure these separately from native runtime
performance so that a faster checker is not mistaken for a faster TypeScript program.

# Language

The subset of TypeScript that Ariadne accepts, what it refuses, and what is proved about drive's
kernel. Everything accepted is covered by the correctness theorem ([DESIGN.md](DESIGN.md)).
Anything else is refused with a diagnostic; `Tests/negative` has one fixture per refusal.

## Accepted

**Types**

- `boolean`, `bigint`, `string`, and `number` as an integer (see Numbers).
- String-literal types and unions of them.
- Optionals: `T | undefined`, `x?: T`, `T | null`, `T | null | undefined`.
- Records (`type` and `interface` declarations of readonly or plain fields).
- Unions of records told apart by a literal field (a string, or `true`/`false`).
- Arrays `T[]` and `readonly T[]`.
- `Map<string, T>`, as the fields of a class.

**Declarations**

- Functions with typed parameters (optional parameters included) and results, calling functions
  declared earlier. No recursion.
- One class whose fields are all `private f = new Map<string, T>()`, with methods (see Classes).

**Statements**

- `const`, `let`, and assignment to `let`s and parameters.
- `+=`, `-=`, `*=`, `x++` and `x--`, as statements on a variable (a number or a bigint).
- `if`/`else`, with braced or single-statement branches.
- `if (x == null) return …;`, narrowing `x` for the rest of the block.
- `switch` on a union's tag or on a literal union: cases in any order, grouped labels, `default` and
  fall-through, narrowing in each case.
- `for (const x of xs)`, `for (const [i, x] of xs.entries())`, and
  `for (let i = 0; i < n; i++)` with a constant `n`.
- `while (c) { … }`, with a condition free of number arithmetic. Its safety condition says that the loop
  ends (see Numbers for how it is discharged).
- `break`, `continue`, and `return` anywhere, including inside loops.

**Expressions**

- Literals, variables, and calls.
- `!`, `&&`, `||` and `c ? a : b`.
- `===` and `!==` on primitives, and `== null`/`!= null`.
- `<`, `<=`, `>` and `>=` on numbers, bigints and strings.
- `+`, `-`, `*` and unary `-` on numbers and bigints; `+` on strings.
- `%` on numbers and bigints, `/` on bigints, and `Math.floor(a / b)` on numbers.
- `??`.
- Field reads.
- Object literals and `{ ...r, f: v }`.
- Array literals with spreads, `xs.length` and `xs[i]` (of type `T | undefined`).
- `includes` on primitives.
- On strings: `s.length`, `startsWith`, `endsWith`, `includes`, `indexOf`, and `slice` with one or two
  arguments.
- `some`, `every`, `find`, `filter` and `map`. Their callbacks are arrow functions with an expression
  body, or declared functions.
- `toSorted` with a comparator.

**Classes**

- `new C()` creates the object with empty maps.
- `this.f.get(k)`, `this.f.has(k)`, `this.f.size`, `[...this.f.keys()]` and `[...this.f.values()]`.
- `this.f.set(k, v);`, `this.f.delete(k);` and `this.m(…);` as statements of `void` methods.
- Methods returning a value may read the state, and may be called inside expressions, but must not
  change it.

## Refused

| Form | Why |
| --- | --- |
| In-place change of an array or record: `push`, `xs[i] = v`, `p.x = v`, in-place `sort` | Arrays and records are values in the model; use spreads and `toSorted` |
| Local `Map`/`Set` | Maps are supported only as class fields |
| `===` or `includes` on objects | Objects compare by identity in JavaScript |
| `this` other than in the forms above | It would share the object's maps |
| Shadowing, a name declared twice | The model resolves names dynamically (see DESIGN.md) |
| Assigning a `const`, a loop variable or a counted loop's bound | Keeps loops and narrowing sound |
| Block-bodied arrows, functions as values other than callbacks | Callbacks may not assign or declare |
| `/` on numbers other than in `Math.floor(a / b)`, `**`, bitwise operators, other `Math` functions, unary `+` | Numbers are integers |
| A declaration named `Math` | `Math.floor` must be JavaScript's |
| A `while` condition with number arithmetic, `do … while` | The condition's safety would join the loop's |
| Non-integer literals, and literals outside ±(2^53 − 1) | Numbers are safe integers |
| `++x`, `x++` inside an expression | Assignments are statements |
| Recursion, `throw`, `try`, `async` | Not yet modeled |
| A constructor with code, more than one class per file, inheritance | Not yet modeled |

## Mutation

- Local variables change by assignment. In the model, assignment replaces the innermost binding; in
  the denotation, it replaces a component of the environment tuple.
- A class's maps change in place through `this.f.set/delete` and `this.m()` in `void` methods. The
  store model, in which the object is changed in place and shared with the methods it calls, is
  proved equal to the value model (`runMethod_store`).
- Nothing else changes in place.
- Nothing can be aliased: arrays and records are values, objects never compare by identity, and
  `this` is never a value.
- Assumed: callers outside the subset do not mutate an object a method returns. It may share
  structure with the class's state, as in JavaScript.

## Numbers

- `number` denotes `Int`. Every result of `+`, `-`, `*` and negation must stay within ±(2^53 − 1),
  where binary64 arithmetic is exact.
  - The model faults outside that range.
  - The function's safety condition (`f.safe`, a hypothesis of its source theorem) requires that it
    doesn't happen.
  - So an overflowing computation is outside the theorem's claim; it is never claimed to compute a wrong
    value.
- `%` and `Math.floor(a / b)` need a divisor other than zero, and `Math.floor(a / b)` safe-integer
  operands; bigint `/` and `%` need a divisor other than zero.
- Comparisons, `===`, `length` and indexing are always safe.
- A `while` loop must end within 2^64 iterations. Prove it with a measure that each iteration decreases
  (`whileSafe_of_measure` in `Ariadne/Lib/Loop.lean`; `Tests/Properties.lean` has an example).
- `bigint` denotes `Int` exactly and needs no condition.
- Negative zero is not distinguished from zero, which is unobservable within the subset.
- Non-integer, NaN or infinite `number` arguments fall outside the theorem's hypotheses: its argument
  relation only admits integers.

## drive's kernel

The motivating programs are drive's `core/kernel` files, copied as fixtures in `Tests/fixtures`.

| File | Changes needed | Proved properties |
| --- | --- | --- |
| `trust.ts` | One: a block-bodied callback lifted into a declared function | `Tests/TrustSpec.lean`: the trust rules (the floor, rotation, which copies count as answered); the exact set of copies a repair may overwrite; and that `chooseVaultCopy`'s safety condition always holds, so every run converges to the readable result with no precondition |
| `registers.ts` | None | `Tests/RegistersSpec.lean`: replaying `pack`, `mark` or `item` changes nothing; two `item` operations on the same album item converge in either order |
| `tree.ts` | None | `Tests/TreeSpec.lean`: positions converge (the latest move wins) and purges converge (the earliest wins); a move and a purge commute; re-deriving where nodes sit never changes either register; `cycleOf` returns exactly the cycles of wanted parents through a node, and finds every one |

Not yet proved for the tree: that the links `rearrange` derives are acyclic and match the wanted
parents outside cycles (the tree-shape invariant).

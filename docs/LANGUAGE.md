# Supported TypeScript

The frontend accepts `.ts` modules containing function declarations and type aliases.
This is deliberately a dialect, not a replacement for TypeScript's full checker.
Functions have explicitly typed parameters and return types. `export` is optional.
Statements require semicolons, and branches and loops require braces (`else if` is
allowed). Local declarations infer types, except empty arrays need annotations.

| Feature | Accepted behavior |
| --- | --- |
| Scalars | `number`, `bigint`, `boolean`, `string`, `undefined`, `null`, `void` |
| Numbers | Decimal literals, fractions, decimal exponents; binary64 including NaN, infinities, signed zero |
| Integers | Decimal `bigint` literals and unbounded signed arithmetic; division truncates toward zero |
| Strings | UTF-16 code units; quoted literals, standard simple escapes, `\xNN`, `\uNNNN`, concatenation and ordered comparison |
| Containers | Dense scalar arrays, scalar tuples, flat records, scalar-key/scalar-value Maps |
| Types | Explicit aliases and scalar unions; optional values can be consumed with `??` |
| Locals | `let`, `const`, assignment; scalar `+=`, `-=`, `*=`, `/=`; number `++`, `--` on local variables |
| Control | `if`, conditional expressions, `while`, three-part `for`, `return`, `break`, `continue` |
| Calls | Named functions, including recursion; supported methods; explicitly typed arrow callbacks |
| Operators | Numeric `+ - * / %`, comparisons, `===`, `!==`, boolean `! && ||`, nullish `??` |

There are no implicit numeric conversions. Conditions must be booleans. `number`
is **not** modeled as an integer or a real. Reference identity comparisons are
rejected. Out-of-bounds reads return `undefined`; integer, dense, in-range writes
are a dynamic model obligation. Missing Map keys also return `undefined`.

## Native operations

| Receiver | Operations |
| --- | --- |
| `T[]` | `length`, indexed reads/writes, `push(x)`, `pop()`, `slice(start, end)`, `map(f)`, `filter(f)`, `forEach(f)`, `reduce(f, initial)` |
| `Map<K,V>` | `new Map<K,V>()`, `size`, `get`, `has`, `set`, `delete`, `clear`, `forEach` |
| `string` | `length`, indexed reads, `charCodeAt(index)`, `slice(start)` and `slice(start,end)` |
| `Math` | `abs`, `floor`, `trunc`, `sqrt` |
| `Number` | Conversion from number/bigint, `isNaN`, `isFinite` |
| `BigInt` | Conversion from number/bigint; nonintegral or nonfinite numbers fail |

`map`, `filter`, and `forEach` callbacks take an element and optional index.
`reduce` takes accumulator, element, and optional index, and requires an initial
value. Map `forEach` takes value and optional key, in that order. Callbacks may
mutate captured scalar locals and unrelated owned containers. They cannot mutate
the traversed collection, return references, escape, call arbitrary named
functions, or shadow outer bindings. A final callback return can refer to local
declarations; more complicated early-return inference is deliberately restricted.

Maps preserve insertion order and use SameValueZero: NaN is equal to itself, -0
and +0 share a key, replacing a key preserves its position, and deleting then
reinserting puts it last. Object identity keys are not accepted.

## Explicit exclusions

Imports, modules spanning multiple source files, JavaScript input, generics,
classes, interfaces, enums, destructuring, spread, templates, regular expressions,
async/await, promises, generators, exceptions/catch, getters/setters, proxies,
reflection, dynamic property names on records, prototype access, `eval`, `any`,
casts, optional chaining, bitwise operators, and overloaded coercions are rejected.
Hexadecimal/binary/octal literals, bigint increments, leading-dot numeric literals,
and mixed nullish/logical expressions are also outside this version.

Aliases, nested references, optional references, and ownership transfers are
conservatively restricted. Returning a borrowed parameter is forbidden. A reference
local must come from allocation, a collection operation that allocates, or a checked
function that returns ownership. A function cannot receive the same collection in
multiple mutable parameter positions. Incoming references must be mutually disjoint.
See [the runtime contract](RUNTIME.md).

The handwritten grammar is not independently proved equivalent to TypeScript's
standard grammar. Native execution tests cover examples and generated programs;
that is evidence, not a universal language-conformance theorem.

# Native runtime contract

Ariadne models native Array, Map and Set operations instead of substituting Lean list
functions blindly. The executable model has an explicit heap, mutable variable
cells, allocation identities, callbacks, and evaluation order. Collection theorems
state when a list abstraction is valid.

A claim about native TypeScript needs the following host assumptions:

1. Start in a pristine realm with conforming native Array, Map, Set, String, Number,
   BigInt, Math, Object, and Function intrinsics. Keep these bindings and the relevant
   prototypes fixed for the entire execution. No external code may interleave effects.
2. Input references are ordinary dense arrays, ordinary Maps/Sets, plain data records,
   or instances of the declared classes
   of the declared shapes. They are not subclasses, proxies, accessors, sparse arrays,
   or objects with own method overrides. Mutable nested values have disjoint owned
   footprints; shared readonly values are never written. Class method definitions
   and their prototypes remain fixed. Map and Set keys are scalar values.
3. Reference parameters are mutually disjoint and exclusively borrowed for the call.
   The outside host must not retain an active alias that mutates during execution.
4. Array writes use nonnegative integer indices no larger than the current length,
   within the native array-index limit. A successful model execution establishes
   this for that execution. Static acceptance alone does not.
5. Ignore allocation/resource exhaustion and engine-specific stack limits. Termination
   and required evaluation fuel are separate proof obligations.

`runtime/realm.ts` supplies an optional **host bootstrap**, not translated code.
Call `hardenPristineRealm()` before any application code in a fresh realm. It freezes
intrinsics, collection iterator prototypes, and global bindings, preventing subsequent
pollution. It cannot recognize or repair pollution that happened before startup,
validate arbitrary incoming proxies, or prove that an engine implements the model.
Freezing shared intrinsics is a host policy decision: use a dedicated worker/realm
for an application that cannot adopt it globally. No runtime import is required by
the translated TypeScript programs themselves.

The checker prevents prototype access and writes, aliases introduced by subset
code, escaping borrows, and mutation of traversal receivers. It currently rejects
user function calls inside callbacks because it has no interprocedural effect
summaries. That conservatism makes snapshot-based traversal modeling appropriate
under the ownership contract; it is not a proof of checker soundness.

The model stops on `typeError`, `rangeError`, or an invariant violation. It does not
model exception handlers or preserve an externally observable heap after an error.
Use successful executions/postconditions when transferring claims. `timeout` is an
analysis result, not an ECMAScript exception or evidence of divergence.

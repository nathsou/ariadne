# What the certificates mean

Ariadne takes a certifying approach. Its native executable writes Lean declarations;
the Lean kernel then checks equations binding the original source to the generated
model. No plugin-provided axiom or native decision procedure discharges those equations.

| Layer | Guarantee today | Remaining boundary |
| --- | --- | --- |
| Lexer/parser | Total Lean definitions; exact per-file source → tokens → AST equations | No independent ECMAScript grammar or universal grammar-equivalence proof |
| Checker | Exact per-file acceptance equation; conservative type/ownership restrictions | No universal preservation/progress or ownership-soundness theorem |
| Emission | Incorrect source/AST substitution fails kernel checking; source certificates are unique | Untrusted printer; generated code is a deep operational model, not a shallow optimized compiler |
| Scalars | Explicit binary64 logical model from Lean core, UTF-16 code units, signed unbounded integers | Conformance of these definitions to an actual JS engine is assumed and differentially tested |
| Heap/control | Explicit state, local mutation, calls, closures, break/continue/return, bounded evaluation | Model errors abstract native error details and discard the failing heap |
| Collections | General map/reduce/list correspondences under callback contracts; Map update laws | Native builtin implementation and host realm assumptions |
| Loops | General invariant-preservation rule, including guard effects and updates | Automatic invariant discovery and termination proofs are not implemented |
| Examples | Arbitrary-integer arithmetic properties; concrete terminating executions and final heaps | Concrete runs do not prove the algorithm for every input |

`Certificate.transfer_at` turns a proved successful model evaluation at a particular
fuel into `SourceReturns`. `transfer_property` transports universally quantified
properties of modeled returns. `SourceReaches` includes the final heap, allowing
proofs about arrays and Maps without exposing allocation addresses to a user.

These source predicates are **defined through Ariadne's operational model**. The
word “source” does not add an unproved equivalence to the ECMAScript specification.
A native-code conclusion additionally needs the runtime contract and a conformance
argument for the model. This boundary is intentional and visible in the API.

`kernel_rfl` constructs a reflexivity proof candidate for a closed equation and asks
the kernel to check it. It does not evaluate native code and does not insert axioms.
A wrong candidate is rejected. `scripts/Audit.lean` checks transitive dependencies
of project theorems, admitting only Lean's standard `propext`, `Quot.sound`, and
`Classical.choice`. `sorryAx`, native-evaluation axioms, and custom axioms fail CI.

Trusted components are the Lean kernel and its standard foundations, faithful
loading of the checked declarations, and the stated interpretation of the model.
For native execution, the JavaScript engine, TypeScript erasure, initial realm,
and input-shape/ownership assumptions are additional boundaries. CI tools are
not part of the proof chain.

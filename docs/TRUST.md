# What the certificates mean

Ariadne takes a certifying approach. Its native executable writes Lean declarations;
the Lean kernel then checks equations binding the original source to the generated
model. No plugin-provided axiom or native decision procedure discharges those equations.

| Layer | Guarantee today | Remaining boundary |
| --- | --- | --- |
| Lexer/parser | Total Lean definitions; exact per-file source → tokens → AST equations | No independent ECMAScript grammar or universal grammar-equivalence proof |
| Checker | Exact per-file acceptance equation; conservative type/ownership restrictions | No universal preservation/progress or ownership-soundness theorem |
| Emission | Incorrect source/AST/compiled-code substitution fails kernel checking; source certificates are unique | The printer is untrusted; certification must finish successfully |
| Shallow extraction | Intrinsically typed Core, kernel-checked elaboration equation and emitted-definition/denotation equality | Until M4, the denotation is the meaning of extracted code; no general equality with the operational model or shallow source-transfer theorem is claimed |
| Scalar compiler | Proof-carrying compilation and general equality with the evaluator at every fuel/input | Smaller fragment; explicit cells, no calls/collections or typed state optimization yet |
| Fuel | All evaluator entry points preserve non-timeout outcomes at larger budgets; convergence and source returns are deterministic | Convergence is defined from evaluator approximations, not an independent ECMAScript semantics |
| Scalars | Explicit binary64 logical model from Lean core, UTF-16 code units, signed unbounded integers | Conformance of these definitions to an actual JS engine is assumed and differentially tested |
| Heap/control | Explicit state, local mutation, calls, closures, break/continue/return, bounded evaluation | Model errors abstract native error details and discard the failing heap |
| Collections | General map/reduce/list correspondences under callback contracts; Map update laws | Native builtin implementation and host realm assumptions |
| Loops | General invariant-preservation rule, including guard effects and updates | Automatic invariant discovery and termination proofs are not implemented |
| Examples | Arbitrary-integer arithmetic and compiled multiplication with a termination bound; concrete algorithm executions and final heaps | Concrete runs for other algorithms do not prove them for every input |

`Certificate.transfer_at` turns a proved successful model evaluation at a particular
fuel into `SourceReturns`. `transfer_property` transports universally quantified
properties of modeled returns. `SourceReaches` includes the final heap, allowing
proofs about arrays and Maps without exposing allocation addresses to a user.

`Executes` describes completed outcomes (success with final heap, or a non-timeout
fault) without selecting a budget. `converges_iff_eventually` proves that a witnessed
outcome persists at every sufficiently large budget. This is adequacy for the
approximation-based definition; no independent operational rule system is claimed.

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

The initial `extract` fragment has scalars, readonly array operations, pure
callbacks/calls, branches, local reassignment, collection iteration and locally
owned updates, borrowed-state threading at direct calls, counted bigint loops,
switches, named records and tagged unions. Its generated `Shallow`
namespace contains definitions over `Int`, `Bool`, UTF-16 `JSString`, binary64
`Float.Model`, `Option`, `List`, ordered `JSMap`/`JSSet` values, and explicit loop
state/exit types. Number-keyed collections use separate SameValueZero wrappers.
Named records become Lean structures with checked constructor/destructor laws.
Core denotation, renaming and substitution are parameterized by a lawful named
interpretation. Record fields are observed by their declared types; absent optional
fields and explicit `undefined` both read as `none`. Property enumeration and
own-property tests are not admitted. Tagged unions become native inductives with
lawful variant representations. Classes use the same lawful record representation;
constructors and explicit receiver functions are included in the kernel-checked
elaboration equation. Mutating methods return updated receiver state.
Its
`ElaborationChecks` and `DenotationChecks` namespaces certify the new links.
Those checks do **not** establish adequacy: an elaborator bug could still choose
the wrong Core, and a denotation bug could still give it the wrong source meaning.
The three-way differential tests provide regression evidence only. The separate
operational `ts_*_source` theorems in the same file retain their existing meaning.

Int53 extraction has a distinct Core type with native `Int` values and executable
`f.safe` predicates. Safety interpretation follows actual calls and control flow;
it remains part of the meaning/trust boundary until M4 relates it to operational
execution. Current predicates retain primitive bit-equality guards in addition
to ranges and nonzero divisors. Thus no general range-only binary64 exactness
theorem is being assumed. Signed-zero results that cannot be represented by an
integer are outside the safe domain. Source transfer remains pending.

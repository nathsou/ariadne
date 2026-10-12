# Shallow translation implementation

The acceptance contract is [DESIGN.md](DESIGN.md). Milestones are complete only
when their exit criteria pass; finite native tests are not universal proofs.

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0 | Complete | Reference sources and historical diagnostics; pinned CI downloads; reserved extraction diagnostics; output preservation tests |
| M1 | Complete | All reference programs check and certify; grammar, ownership checks, operational semantics and the builtin table have differential coverage. Conservative dialect limits are listed below. |
| M2 | In progress | Typed Core, scalar/list/Map/Set extraction, owned local updates, structural loops, pure calls, structural denotation, three-way differential and tamper tests. Lawful named records/unions and direct borrowed-state calls are implemented; class states, Int53 guards and original reference extraction are implemented; the full integration regression gate is pending. |
| M3 | In progress | The original decision extraction has universal membership, floor and permutation proofs. Register/tree proofs and general Int53 exactness lemmas remain pending. |
| M4 | Pending | Fundamental lemma, footprint preservation, adequacy and source transfer |
| M5 | Pending | Measures, larger ownership, polymorphism, exceptions and scalar backend integration |

## Reference specifications

`examples/reference/baseline.json` records diagnostics at the design commit. It is
historical evidence, not an assertion that the programs should remain rejected.
`scripts/reference.mjs` exercises the native specification of each reference.

- Decision equality is structural: candidates with the same version and id are
  the same result value, even if allocated separately.
- Register convergence assumes stamps identify consistent operations. Counters
  are per-replica monotone components merged by maximum. Composite key components
  exclude NUL; arbitrary strings would make the encoding non-injective.
- Tree correctness is an invariant of states reachable from a fresh instance.
  Moving to a descendant detaches the moved node. Lookups, rather than Map
  insertion order, specify observable agreement.

## Validation

M0: `scripts/check.sh` passes, including 1,072 audited theorems, the existing
operational and scalar comparisons, adversarial certificates and diagnostics, and
1,728 native tree traces. Lean 4.34.1 and Node 24.19.0 were used locally.

## Current frontend limits

- Iterators returned by `keys`, `values` and `entries` are consumed immediately by
  spread or `for…of`. They are distinct from arrays; storing a live iterator is
  rejected until the checker tracks its lifetime.
- Template interpolation supports all scalar types. Decimal binary64 formatting
  is modeled with integer arithmetic and tested at decimal boundaries and their
  adjacent floats. Array `join` currently accepts scalar elements.
- Switch clauses must exit explicitly; grouped labels and implicit fallthrough are rejected.
- `@decreases` is preserved and typechecked, but is not a termination proof on
  the operational path. Tier-1 extraction is still pending.
- Sorting uses a stable merge and requires a consistent comparator for agreement
  with every native engine. Undefined elements are placed last without invoking
  the comparator. Callback element references are shared read-only borrows.
- The type/ownership checker still has no general soundness theorem. M4 must
  establish adequacy before extracted definitions can support source claims.

Frontend checkpoint: the complete `scripts/check.sh` suite passes with 1,217
audited theorems, 42 native entry points, 64 generated programs, 51 scalar
comparisons, 37 negative fixtures, and 21 reference inputs/traces. All three
reference operational certificates build in CI. This is not M2–M5 completion.

The completed M1 builtin checkpoint passes the full suite with 1,582 audited
theorems, 50 native entry points, 46 negative fixtures, and 2,428 binary64 decimal
formatting comparisons. It covers short-circuit callback searches, stable sorting,
string searches and position clamping, concatenation and scalar joining, variadic
Math extrema, signed zero, and numeric templates. The fuel monotonicity proof
includes the new search, merge and sort evaluator clauses.

## Initial extraction fragment

`extract` now accepts pure scalar functions with local reassignment, branches,
bigint addition/subtraction/multiplication and comparisons, binary64 arithmetic,
UTF-16 string operations, and optional scalar values. Arrays lower to lists, with
indexed pure callbacks, map/filter/reduce/search, indexing, slicing, reversal,
concatenation and spread. Calls with scalar or immutable parameters are accepted.
Branch continuations are shared through typed tuple arguments. Array `for…of`,
counted bigint loops, scalar switches, and nested break/continue/return lower to
typed `Step`/`Exit` combinators. Maps and Sets have scalar keys, insertion-ordered
iteration, reads, and locally owned updates. Owned array `push` becomes append.
Named records and tagged unions have lawful native representations. Mutated
borrowed parameters are returned as state components and rebound at direct calls.
Classes lower to named field records with explicit receiver state and constructors.
Files declaring `type Int53 = number` opt into the integer refinement. Counted
Int53 loops accept stable scalar or collection-size bounds. Arbitrary number
loops still require a termination/refinement argument.
This is an incremental M2 slice, not the M2 reference-program exit gate.

The extraction checkpoint passes the complete `scripts/check.sh` suite: 1,559
audited theorems, 39 negative fixtures, and 38 additional three-way scalar
comparisons. A 20-branch stress case checks continuation sharing and closed
results in the kernel. Each shared continuation has its own denotation lemma;
the function certificate composes these lemmas without expanding all paths.

Generated modules contain an intrinsically typed Core term, an elaboration
equation checked by the kernel, native definitions, and per-function denotation
equations. Extraction checks a temporary candidate before replacing output.
The current denotation remains a trust boundary until M4. The scalar proof
examples prove properties of emitted definitions only and do not claim source
transfer.

The collection prelude has insertion-ordered Map/Set representations carrying
key-uniqueness proofs, lookup and update laws, insertion-order/size lemmas, and
lookup equivalence. Array proof examples
establish a fold specification and permutation invariance of a sum, a transform's
nonnegativity, and a pure call's result directly over emitted definitions.

The array checkpoint passes the full suite, including 51 new three-way cases
and readonly input preservation. Core renaming and substitution preservation are
also proved and included in the axiom audit (1,878 theorems after adding these
lemmas). Emitter tests cover source names that overlap generated metadata and Lean
type/helper names. These checks still do not establish operational adequacy.

The optional-value checkpoint adds flow-sensitive narrowing through early returns,
short-circuit conditions and ternaries, invalidation after reassignment, and block
scope preservation. The full suite passes with 57 scalar extraction comparisons
and 51 frontend entry points. A parser regression now covers compound conditions
before a ternary. The numeric-key prelude proves SameValueZero equivalence and
positive-zero canonicalization against the operational definitions, without
changing IEEE equality used by source `===`.

Loop proof examples establish the emitted sum's fold specification and append
law. The prelude supplies invariant, fold, congruence, mapped-input, and exact
integer-range lemmas. Counted-loop extraction checks that the bound is stable
and that only the update step assigns the counter. Frontend return analysis now
tracks normal, return, break and continue outcomes, including exhaustive switches
and unreachable statements after a break.

The loop checkpoint passes the full suite, including 44 new three-way loop cases,
57 scalar cases, 51 array cases, and 48 negative fixtures. Native loop proofs also
establish sum permutation invariance and first-match membership/floor properties.
The numeric collection wrappers prove update/lookup laws, idempotence, NaN
membership, and positive-zero insertion behavior. Their subsequent library build
and expanded axiom audit pass with 2,135 theorems.

The collection checkpoint passes the full suite with 2,392 audited theorems and
49 additional three-way cases. It checks insertion order, NaN and signed-zero
keys, deletion, clearing, entry tuples, nested stored arrays, local array pushes,
and preservation of readonly input heaps. The emitted histogram has universal
fold, count, membership and permutation/lookup-equivalence proofs. Entry spreads
copy fresh tuples with immutable members; copying nested mutable owners remains
rejected. Shallow certificates are built serially to bound CI memory use.

Named record extraction emits Lean structures, constructor/destructor functions,
and both inverse laws. Named declarations include their canonical shape, and Core
denotation plus the renaming/substitution theorems work for every lawful
interpretation. Record extraction supports optional fields, fixed literal tags,
callbacks over records, and lists of records. It preserves last-initializer-wins
behavior and safely renames Lean-reserved field names. The new 19-case differential
suite compares declared-field observations and checks that input heaps are
preserved. Native proofs cover field preservation, update composition, sum
permutation invariance, and first-match membership/floor properties. These remain
native properties, without a shallow source-transfer claim.

The record checkpoint passed the full local suite and CI with 2,622 audited
theorems. The next slice adds native tagged inductives, typed variant views,
reinjection into parent unions, discriminant narrowing and switches, including
three or more variants. Its 55 three-way cases cover construction, optional
fallback, reassignment, filtering and decision-input permutations, with input
heap preservation. The frontend's common-field lookup now descends through
nested unions and retains readonly collection qualifiers.
Native proofs establish the bigint decision fixture's fold specification,
input membership, valid-only output, and floor bound for arbitrary inputs.
The original Int53 reference program and its permutation theorem remain pending.

The union checkpoint passed the full local suite and CI with 2,804 audited
theorems. Borrowed-state extraction now returns each updated mutable parameter
alongside the source result. Direct calls restore the caller's owners, including
calls inside loops and early-return paths. Read-only calls retain their ordinary
result type. A 36-case three-way suite compares both results and caller-visible
heaps for Maps, Sets and arrays. Native proofs cover increments, preservation of
other keys, repeated calls, transfers, fresh results and array append. Reassigning
a mutated borrowed parameter, nested borrowed arguments, and effectful calls
inside larger expressions still have explicit extraction refusals.

## Class extraction checkpoint

Class fields become a named native record. Constructors initialize fresh state;
methods that mutate the receiver return its updated state. Direct method calls,
scalar field assignment, and owned collection-field updates share the existing
state-threading path. Calls between methods and calls on borrowed class parameters
are supported. Generated constructor/initializer names cannot collide with source
method names.

Ten three-way constructor/method traces observe intermediate states, including
early returns and UTF-16 keys. Native proofs cover initialization, update/frame
laws, method composition, and borrowed calls. Method bodies with readonly array
parameters are tested through the operational evaluator; the frontend still
rejects reference arguments at class-method call sites. Nested receiver expressions
and nested collection loans remain outside this extraction slice.

The preceding borrowed-state checkpoint passed the complete suite with 2,981
audited theorems and green CI. The class checkpoint also passed the full local
suite and CI, with 3,145 audited theorems. Operational adequacy remains the separate M4 gate.

## Int53 and original-reference extraction

The exact `type Int53 = number` declaration enables the refinement, including
aliases of it, integer literals, lengths, sizes and counted-loop counters. The
frontend preserves the distinction from both `number` and `bigint`; widening to
`number` is implicit. Floor/truncated Int53 quotients and remainder have integer
denotations. Optional scalar equality supports the tree's cursor comparison.

Each emitted function has an executable `f.safe` predicate. Its interpreter
collects conditions along actual branches, loop exits and callback invocations,
including short-circuit searches. It checks refined inputs, operation ranges and
nonzero integer divisors. Primitive arithmetic also retains explicit binary64
bit-equality guards: general range-only exactness simplification lemmas are still
pending in M3. These guards distinguish signed zero. In particular, `(-1) * 0`
and `-0` cannot be represented by the canonical integer zero; both are rejected
by their safety predicates, with kernel-checked counterexamples to a range-only
claim. Runtime Int53 input representation will likewise use canonical positive
zero in M4.

The three original references now extract and pass kernel checking. Three-way
tests cover 98 decision inputs, 25 register/tree traces with intermediate state
observations, and 52 numerical safety cases. Native numerical proofs cover
arithmetic equations and both accepted and rejected safety paths. These tests do
not replace the universal reference theorems or operational adequacy.

Local Lean 4.34.1 module builds took 36 seconds for decision, 24 seconds for
registers, and 42 seconds for tree. These timings include source, frontend, Core
elaboration and denotation checks together; they are not isolated tactic timings.
The full integration suite is pending.

The original emitted decision program now has universal fold, membership,
floor-bound, valid-only and permutation-invariance theorems in
`Examples/Proofs/ReferenceDecision.lean`. They reason over native data and
structural folds, independently of heap addresses or evaluator fuel.

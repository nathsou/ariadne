# Shallow translation implementation

The acceptance contract is [DESIGN.md](DESIGN.md). Milestones are complete only
when their exit criteria pass; finite native tests are not universal proofs.

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0 | Complete | Reference sources and historical diagnostics; pinned CI downloads; reserved extraction diagnostics; output preservation tests |
| M1 | Complete | All reference programs check and certify; grammar, ownership checks, operational semantics and the builtin table have differential coverage. Conservative dialect limits are listed below. |
| M2 | Complete | Typed Core, scalar/list/Map/Set extraction, owned local updates, structural loops, pure calls, structural denotation, three-way differential and tamper tests. Lawful named records/unions and direct borrowed-state calls are implemented; class states, Int53 guards and original reference extraction are implemented; the full integration regression gate passed. |
| M3 | Complete | All three original reference acceptance proofs hold universally over emitted definitions. The native proof library includes loop, collection, string and stable-sort laws, and general Int53 arithmetic correspondence, including rounded nonintegral division. |
| M4 | In progress | Heap framing, compositional data relations and external-heap source predicates are proved. Scalar expression correspondence and generated source transfer are proved; the stateful ownership environment has declaration, reassignment and framing laws. Full stateful/data adequacy remains pending. |
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

The second-class-reference checkpoint rejects parameter/receiver reference
escapes through aliases, conditional returns and immutable storage annotations.
It also rejects local bindings of mutable container observations and readonly
views of mutable elements used as stored or returned values. Copies remain
owners; deeply immutable element observations may be shared and returned.
`OwnershipEnvironment` relates visible source cells to current native values,
excludes binding cells from data footprints, and distinguishes owners, call
borrows and observations. Declaration, reassignment, projection and framing
laws are kernel checked. This relation is currently conservative about shared
immutable descendants inside writable owners; its integration into general
stateful source transfer and the checker soundness theorem is still pending.
`PermissionEnvironment` refines this relation with separate read and write
footprints. Every existing ownership witness embeds into it. Declarations,
binding-cell reassignment, scope exit and temporary projection framing preserve
the refined invariant. Other values are framed using write/read separation,
even when their read footprints share immutable descendants. Computing those
permissions from checked types and proving the checker fundamental lemma remain
open; these are environment laws rather than a complete adequacy theorem.

Export guard checkpoint: extraction emits a sibling TypeScript runtime module,
kernel-bound wrapper text, and per-export checked guard plans, `entrySafe` and
fuel-indexed wrapper models. Plans use effects after class lowering and original
types for containment; private class fields are opaque. Containment is checked
in both directions, including a readonly argument nested inside a mutated one.
The operational guard throws before the implementation on overlap. Its success
is equivalent to guard success followed by the original invocation. A proved
ownership-tree/public-path rule derives footprint separation from a passing
guard and structural `EntryShape` facts, without assuming input disjointness.
Deriving those facts from checker soundness and integrating write/read footprint
permissions into general stateful transfer remain M4 obligations. This does not
complete adequacy, projections or M5.

Projection proof foundation: partial lenses for ordered Maps and arrays satisfy
get/put, put/get, repeated-put, modification and composition laws. Element and
Map-key focus rules rebuild container representations while framing all other
elements. Array-of-arrays and Map-of-arrays push rules prove actual operational
invocations, retain the outer runtime references, and write only the selected
inner array. Single-statement projections now parse, check and lower through
one key binding and one selected-value binding. Mutable references cannot
outlive the statement; a second use of the same container and impure keys or
update arguments are rejected. Compound updates evaluate the source receiver
once, read the old value before the right operand, and write into the resulting
heap. Missing elements fail the computed safety predicate. The native runtime
updates the existing inner object without copying it; Lean uses pure container
replacement. Differential checks cover arrays, Maps, record-field updates,
binary64 edge cases, selected-element identities and missing-element guards.
Exported three-parameter `Map<string, bigint[]>` pushes now receive a universal
stateful source theorem over the actual input heap representation and computed
`f.safe`. Its conclusion observes the actual emitted native state in the final
source heap. A second theorem lifts the result through the kernel-bound runtime
wrapper and its operational entry guard. Neither has input disjointness or
whole-function execution as a premise. Three forged state/guard/entry witnesses
are checked against a dedicated one-function fixture. General data/state/class
source transfer and checker soundness remain M4 work. Simultaneous projected
call arguments remain pending.

CI #96 on `5e31ceb` passes in 11m23s, compared with baseline CI #82's 21m18s.
Its logged source-transfer and Int53 tamper phases take 17s and 7s respectively,
compared with the baseline 1m51s and 1m29s. The axiom audit covers 5,435 theorems.
CI #102, including wrapper certificates and the projection proof foundation,
passed in 12m49s; its tamper phases take 14s and 6s. Its example jobs were uneven
(328s versus 172s), so unions, records and entry-guard fixtures now run in the
data job. Each runner still kernel-checks its own files serially.
The subsequent local projection gate passed all 26 JavaScript suites and a
6,594-theorem axiom audit. CI now runs basic verification, data comparisons and
source/tamper checks on separate runners after restoring the checked artifacts.
Every runner remains serial, and the final required status rejects a failed or
skipped phase.
CI #104 on `76ae948` passed the split in 12m00s (baseline: 21m18s), including
all 26 suites and 20 new projection comparisons. Source/Int53 tamper phases
took 21s/9s. Shared-continuation tamper checks still took 73s, so their four
unchanged assignment/capture/restoration/comparison mutations now use a
dedicated two-function fixture while all eight universal source theorems and
50 three-way comparisons remain checked.

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
The full integration suite passed with 3,830 audited theorems.

The original emitted decision program now has universal fold, membership,
floor-bound, valid-only and permutation-invariance theorems in
`Examples/Proofs/ReferenceDecision.lean`. They reason over native data and
structural folds, independently of heap addresses or evaluator fuel.

The original register extraction now has universal idempotence and permutation
convergence proofs in `Examples/Proofs/ReferenceRegisters.lean`. Operations use
the emitted methods, and convergence covers mixed writes and counter updates
from any initial state. Equal encoded keys and stamps must identify equal values.
The conclusions include both emitted read accessors and preserve the distinction
between absent counter entries and stored values. The string prelude proves
composite-key injectivity when the first components exclude the delimiter.

The original tree extraction has a universal child/parent agreement theorem for
all states reachable through the emitted constructor, `add` and `move` methods.
Its emitted root walk reaches a parentless node within the node count for closed,
acyclic parent graphs (acyclicity is expressed by a decreasing natural rank).
Every reachable move preserves closure and acyclicity. A missed bounded search
excludes reachability of the moved node from the target; attaching the new edge
then admits an explicit decreasing rank. `reachable_root` therefore applies to
every reachable state, including detach-on-cycle moves. These remain native
proofs until M4 supplies source transfer.

M2 integration gate: the full `scripts/check.sh` run passed with all original
references extracted, certified and compared, including 52 Int53 safety cases,
98 decision inputs and 25 original class traces. The audit accepted 3,830
proofs using only standard Lean logical axioms. The native reference proof
checkpoints are included in this run; operational adequacy remains M4.

The prelude now includes string strict-total-order and concatenation laws,
loop composition/invariant/fold laws, Set lookup congruence, Map deletion order
and entry folds, and stable merge-sort properties under explicit comparator
conditions. `Loop.each_append` requires a break-free prefix: `Exit.done` erases
whether a loop stopped early, so unconditional concatenation would be false.
The sort lemmas concern the pure native prelude; the operational sort bridge is
part of the pending adequacy work.

`Prelude/Int53Exact.lean` derives canonical safe-integer representations from
Lean's binary64 packing and rounding model. Kernel-checked universal lemmas now
cover comparison, conversion injectivity, exact addition/subtraction/multiplication, absolute value, and negation with the
necessary nonzero condition. They use range hypotheses, not primitive equality
guards. Exact exponent scaling is proved for the remaining arithmetic work;
multiplication preserves canonical zero under `CanonicalProduct`; remainder exactness is proved under `CanonicalRemainder`. Quotient rounding remains pending.

CI found a NaN-observation portability bug in the new Int53 harness: Bun returned
a negative NaN for division by zero while the model canonicalizes NaNs. The
harness now uses the same NaN normalization as the existing differential suites,
while preserving exact signed-zero comparisons. The corrected 52-case harness
passes under Node 24.19.0 and pinned Bun 1.3.5; original-reference comparisons
also pass under Bun. The numeric exactness checkpoint builds and audits 3,885
theorems. Fresh CI is pending.

The numeric library also proves that truncation and floor leave canonical safe
integers unchanged, conversion back to `Int` is exact, and integer quotients and
remainders remain in range. List lengths below the JavaScript array bound are
proved to fit Int53. The remaining numeric correspondence is floor/truncation of
rounded nonintegral binary64 quotients.

`Examples/Proofs/Int53Safety.lean` discharges the actual emitted `.safe`
predicates for addition, multiplication, negation and remainder from ordinary
range/divisor/signed-zero hypotheses. These are universal proofs over symbolic
inputs, not closed executions. The arithmetic library checkpoint audits 3,909
theorems before adding these safety examples.

Division is now proved exact when the mathematical quotient is integral, including
its floor/truncation wrappers and the canonical-zero condition. Nonintegral
quotient rounding remains the numeric proof still in progress.

## Operational adequacy foundations

`Heap.lean` proves that allocation preserves existing observations and that writes
inside an owned footprint preserve disjoint, allocated footprints.
`Shallow/Represents.lean` composes these laws for scalar values (including canonical
Int53 zero), options, arrays, maps, sets, source-named record fields, unions and
class state. Runtime layouts are explicit: a Core pair does not by itself say
whether the source stored a tuple or record, nor retain its field names. Owned
children have disjoint footprints and exclude their root address; numeric
collections additionally require normalized keys. Named representations work
for every lawful interpretation. Allocation and framing theorems are proved.

`SourceFrom.lean` adds budget-independent calls from existing states, retaining
final states for class traces, and `SourceReturnsFrom` for external input heaps.
Execution is defined using the existing evaluator and `Converges`. Determinism,
eventual agreement, certificate transfer and compatibility with `SourceReturns`
on the empty heap are proved. Input representation remains an adequacy premise,
not a claim made by the raw execution predicate. These are foundations: no
generated function has an operational adequacy theorem yet.

CI #58 passed the complete suite after the NaN harness correction. The subsequent
integral quotient and emitted safety proof checkpoint built and audited 4,133
theorems. Nonintegral quotient rounding remains open; its explicit primitive
bit-equality guard remains in generated safety predicates.

The foundation checkpoint builds `Ariadne` and `Examples` and passes the axiom
audit (4,206 theorems). `Convergence.lean` proves compositional evaluation rules
for strict scalar operations, conditionals, short-circuit boolean operators and
member/index reads. These rules preserve source evaluation order and combine
finite witnesses through the existing fuel monotonicity theorem.

## First generated operational source theorems

`Adequacy/Scalar.lean` proves the fundamental expression lemma by induction on a
source/Core correspondence witness. Its supported scalar primitives, conditional
choices and boolean short-circuiting converge in the original evaluator and
preserve state, for every lawful interpretation and matching environment. The
function bridge proves parameter-cell binding and call-frame behavior. The
printer now emits checked witnesses and `f_source` for functions consisting of a
return of a supported scalar expression; it does not assert adequacy for the
remaining fragment. No whole-program execution assumption occurs in these
theorems. The original decision/register/tree transfers are still pending.

The new `source.ts` fixture covers ten universal emitted source theorems. Native
algebraic and short-circuit facts transfer to the original source for arbitrary
inputs and arbitrary initial heaps. A user function named `choice_source`
exposed a name collision in the legacy operational emitter as well; both emitters
now preserve the user name and place the colliding theorem in a namespace.
Three additional tamper checks alter primitive rules, parameter bindings and
source-function selection, independently of the existing source/Core/native
certificate checks.

Array length and indexed reads are now proved against heap representations;
index coercion covers every binary64 input and returned elements borrow a
sub-footprint. Map lookup likewise agrees with native ordered lookup under the
scalar key equality relation. Bigint, string, boolean and SameValueZero number
keys discharge that relation directly. These primitive lemmas do not yet supply
whole-function transfer for collection code.

The full `scripts/check.sh` run passed under pinned Bun 1.3.5, including all
generated certificates, 4,518 audited theorems, ten generated universal scalar
source theorems and their three tamper checks, all differential suites, and all
original-reference comparisons. The original references still lack source
transfer; this gate verifies the current partial M4 coverage.

The structural loop bridge now relates `Loop.each` to operational `eachBody`
and `for…of`, including continue, break, return and lexical-environment
restoration. It consumes the actual visited guards and a local body
correspondence; it does not assume execution of the whole loop or require a
fixed body budget. State relations can carry heap/ownership invariants. Separate
lemmas prove that collecting guards preserves loop, fold, map/filter and search
values. The generic Core/body correspondence needed to apply this bridge to all
extracted loops remains pending.

Map and Set deletion-size laws, including SameValueZero numeric wrappers, now
use the unique-key invariant. Int53 map-key equality follows from the proved
binary64 comparison theorem and both key range hypotheses.

## General Int53 quotient correspondence

The remaining nonintegral quotient proof is complete. `toInt_div` proves that
conversion of the actual rounded binary64 quotient agrees with `Int.tdiv`.
`trunc_div_exact` and `floor_div_exact` prove the actual `Math` wrappers agree
with integer division under explicit canonical-zero conditions. The proof bounds
binary64 rounding at a common power-of-two scale and shows that a nonintegral
quotient stays strictly between the same consecutive integers. It then follows
the model's packing, unpacking, comparison and conversion definitions. No
primitive bit-equality hypothesis or new axiom is used.

The emitted `truncDivide.safe` and `floorDivide.safe` predicates are discharged
from range, nonzero-divisor and signed-zero premises for arbitrary inputs.
`lake build Ariadne Examples` passes, and the audit passes at 4,576 theorems.
Together with the existing native reference and prelude proofs, this closes M3.
M4 remains partial: the general stateful/data correspondence and reference
source transfers are still required. M5 has not been completed.

## Scalar statement source transfer

The correspondence witness now covers fresh local declarations, nested blocks
that return, conditional early returns and unreachable suffixes. The proof uses
compositional convergence rules for the original `exec`/`execBlock`, accounts
for allocated binding cells, and restores lexical scopes and caller frames.
Generated witnesses refer to the actual source statement list and typed Core
body. Reassignment, shadowing and shared continuations still need a richer
environment relation; the emitter does not claim transfer for them.

The source fixture now contains fourteen universal emitted theorems. Native
facts about local arithmetic, early returns and nested branches transfer for
arbitrary inputs and initial heaps. Five kernel tamper tests cover primitive
rules, input bindings, function identity, local names and branch conditions.
The targeted source proof build and all five tamper checks pass.

Record access now has a borrowed-footprint correspondence theorem, with
compositional field projections. `defaultField` handles both absent optional
fields and explicit `undefined`; class fields retain the required-field layout
because the operational model interprets absent class members as methods.
Replacing an owned root preserves disjoint child observations and framed heap
objects. These primitive laws do not establish whole-record/class adequacy.

The complete pinned-Bun `scripts/check.sh` run passes for the scalar statement
and record checkpoint, including 4,658 audited theorems, all generated modules,
fourteen source-transfer examples and five tamper checks, every differential
suite, all original-reference comparisons and 2,428 formatting cases. CI #70
also passed the preceding complete M3 checkpoint.

## Scalar reassignment correspondence

`Bindings.lean` proves allocation and separation of visible binding cells,
preservation under declaration and writes, and lookup laws for assignment.
The scalar environment relation now hides stale Core versions when a source
name is rebound. Function parameter binding establishes the cell invariant
without restricting the initial heap. The statement fundamental lemma and
emitter now cover scalar reassignment, including repeated updates and early
return branches; source-level shadowing remains a frontend restriction.

Eighteen universal source fixture theorems compile. Native facts transfer for
repeated updates, preservation of another local variable, conditional assignment
and string reassignment. All six tamper checks pass, including an altered
assignment target. Shared continuations, collection/state/class code and Int53
still require further correspondence rules.

`Safety/Scalar.lean` proves scalar value erasure for typed Core expressions,
including arithmetic guard terms, local bindings, conditionals and closed
terms. Lifting a native data environment establishes its relation to the safety
environment. An accepted visited guard is proved true in the native denotation;
this supplies a prerequisite for guarded Int53 operational correspondence.

Validation for this checkpoint passes: all shallow and original-reference
artifacts, `Ariadne` and `Examples`, 4,735 audited theorems, the shallow
three-way comparisons, and all eighteen source examples and six tamper checks.
CI #72 also passed the preceding statement/record checkpoint.


## Guarded Int53 source correspondence

`CallConvergence.lean` composes actual callee, argument and invocation convergence
without a user-visible budget. `Adequacy/GuardedScalar.lean` proves scalar
correspondence under the guards computed by `Safety.term`; `GuardedStatements`
extends it to declarations, reassignment and early-return branches. The integer
wrapper's bit equality establishes canonical binary64 results, including signed
zero. Comparisons use the primitive Int53 laws. Unary Math calls check actual
builtin resolution in the caller frame and program table.

Fourteen guarded Int53 fixture theorems are emitted, including arithmetic,
nonintegral floor/trunc division, comparisons, local bindings, repeated updates
and conditional early returns. Six arithmetic properties transfer to the
original source for arbitrary inputs and initial heaps using ordinary range and
canonical-zero hypotheses. All fourteen generated theorems, three kernel tamper
checks and 63 differential safety/operational/native comparisons pass.

Math extrema, shared continuations and full collection/state/class transfer
remain outside this operational fragment. M4 is still partial and M5 is pending.

The guarded checkpoint's complete artifact rebuild, `Ariadne`, `Examples` and
`Tests` build, 4,851-theorem axiom audit, shallow differential gate, and original
scalar source gate (eighteen theorems and six tamper checks) all pass. CI #74
passed the preceding reassignment checkpoint. Project regeneration is current.

## Owned push and structural function erasure

`Adequacy/ArrayMutation.lean` composes disjoint element footprints through append
and proves original array `push` invocation correspondence. An inserted owned
value must be separate from the old array; capacity is explicit. The resulting
array represents the native append, only its root is written, and framed heap
observations remain valid. This is a primitive mutation law, not whole-array
function transfer.

`Safety/Erasure.lean` relates guarded and native values at every Core type,
including functions by their action on related inputs and containers retaining
function values. All unary and binary primitives preserve the relation. Value
erasure is proved for the structural fragment containing functions, application,
options, lists, products, sums and scalar control flow. Renaming, substitution,
projection and continuation abstraction preserve the fragment. Callback
traversal, named construction and the general source-control relation remain
required before claiming a complete fundamental lemma.

Both modules and `Ariadne` build successfully. The dependency audit passes for
4,916 theorems using only standard Lean logical axioms.

## Full Core value erasure

The fragment restriction on value erasure is removed. `Erasure/Traversal.lean`
relates all collection callbacks and early-exit iteration; `Erasure/Data.lean`
proves native data lifting and named-shape cast correspondence; `Erasure/Term`
proves the fundamental value lemma by induction on every typed Core term.
Guarded function values retain their invocation guards and agree with native
functions on related inputs. The result holds for every named interpretation,
even when a computed guard fails. The earlier structural witness is retired.
This closes the safety-value/denotation relation; the general operational
source fundamental lemma and reference-program transfer remain open.

`Prelude/Measured.lean` supplies the well-founded/fuel bridge needed for M5:
every continuing step strictly decreases a natural-number measure, and fueled
iteration agrees with well-founded recursion at every budget above that measure.
Stop and return branches require no decrease. This is a proved library foundation;
measured source lowering and `termination_by` emission are not implemented yet.

The full Core erasure modules, measured-loop bridge, `Ariadne`, `Examples` and
`Tests` build successfully. The theorem-dependency audit passes with standard
Lean logical axioms only.

## Array capacity and writable type preservation

Core array cons and append collect a capacity guard; the original evaluator
checks the same limit when allocating literal/spread arrays and concatenation.
`Safety/Capacity.lean` proves that accepted guards bound the actual native
result length below 2^32. Synthetic counted-loop ranges remain unbounded by
array capacity because they do not allocate source arrays.

The frontend previously accepted an existing mutable Int53 array, Set or record
through a wider number parameter, allowing a callee to insert a non-integer.
`borrowedCompatible` preserves writable element/field types for existing mutable
arguments, including constructors. Fresh allocations and readonly observations
retain their existing conversions, and record width subtyping preserves writable
field types. Three new negative fixtures reproduce and reject the unsafe cases.
All 53 negative fixtures, project regeneration and shallow/reference artifact
builds pass. The audit accepts 4,968 theorems. The full gate caught an eager
argument-inference regression for fresh empty arrays; inference now runs only
for existing mutable arguments. All 21 reference operational comparisons pass
after that correction. The complete regression gate passes, including all
source/representation tamper checks, shallow differential suites and reference
traces. CI #82 passed this checkpoint.

## Optional observations and shared source continuations

Optional reads now flatten absence and present undefined payloads consistently
for arrays, maps, callbacks and record fields. Undefined-only unions retain their
unit representation, while literal strings inside containers and optional fields
retain strings. Coercions and comparisons still evaluate undefined-valued operands
so their arithmetic safety guards are preserved. Ambiguous nested empty-object
views require a named runtime representation. The optional suite covers 55
comparisons, borrowed heap preservation, retained guards and extraction refusal.

`Adequacy/Joins` and `JoinsContext` connect actual shared Core continuations to
the original source evaluator. Typed captures, scalar assignments, early returns
and lexical restoration are checked explicitly. Closed continuations are reused
without duplicating their bodies. The scalar fixture now transfers update and
scoped functions; eight additional shared-control functions have universal source
theorems and 50 differential comparisons. Four forged witnesses are rejected.

`GuardedJoins` and `GuardedJoinsContext` preserve the invocation guard of each
captured function. `Safety/Structural` proves renaming, safe substitution and
continuation abstraction for the complete Core syntax. Eight guarded functions
transfer under their actual computed safety predicates. Forty comparisons cover
safe branches, overflowing shared suffixes and negative-zero multiplication;
three forged witnesses are checked against a dedicated one-function fixture.

The 20-branch stress artifact stays below 300,000 bytes and kernel-checks in
about 37 seconds with 3.2 GiB peak memory. Its final theorem reuses the already
proved denotation equality instead of expanding both sides of every branch.

`SourceData` observes data results in the final operational heap. `ReadExpr`
proves syntax-directed correspondence for scalar expressions, array length,
ordinary and flattened optional indexing, and represented record projections.
This is a data-read foundation; general mutation, state/class and reference-program
source transfers remain open. M4 is still in progress.

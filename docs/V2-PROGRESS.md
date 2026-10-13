# Ariadne v2: progress

Companion to [V2-DESIGN.md](V2-DESIGN.md). Records what exists, where the implementation departs from the design and
why, and measurements. Update it with each milestone.

## Status

| Milestone | State |
| --- | --- |
| M0: measurements, CI | Kernel-cost measurements below. CI job `v2` runs `scripts/v2-check.sh` and is part of the required `verify` status. |
| M1: L0 end to end | Done: model, typed syntax, erasure, denotation, general theorem, frontend, CLI, fixture, differential and negative tests. |
| M2: L1 | Done: records (literals, `{ ...r, f }`, field reads), string-literal unions, tagged unions (string or boolean tags) with `switch` narrowing, optionals (`?:`, `T \| null`, `T \| null \| undefined`), `== null` narrowing in expressions and statements, `??`, optional parameters, `break` in `switch`. Theorem, frontend, fixture, differential and negative tests. |
| M3: L2 | Done: integer-mode `number` with safety conditions, array literals with spreads, `length`, indexing, `includes`, `some`/`every`/`find`/`filter`/`map` with arrow callbacks, `toSorted` with a comparator. Theorem, frontend, fixture, property proof, differential and negative tests. |
| M4: L3 | Done: `let`, assignment (including `+=`, `++`), `for…of`, `for (const [i, x] of xs.entries())`, `break`/`continue`, early `return` in loops, `switch` in loops. Theorem, frontend, fixture, property proof, differential and negative tests. Counted `for` deferred (see the checkpoint). |
| Checkpoint after M4 | Written below: continue. |

### Toolchain

The only external tools are Lean 4.35.0 (with Lake) and Bun 1.4.3, both the latest releases, downloaded by
`scripts/install-ci-tools.sh` and checked against pinned SHA-256 hashes. elan is no longer used. (GitHub Actions'
own `checkout`/`upload-artifact` actions, pinned by commit, are CI infrastructure.)

### M2 notes

- **The model now covers L1 to L3** (records, arrays and their methods, integer-mode numbers, callbacks, `switch`,
  `break`/`continue`, `let`, loops), validated against Bun by `V2Tests/model/*.ts` (`scripts/v2-model.mjs`): every
  `t_*` function agrees, every `fault_*` function is refused by the model. Writing the trusted model in one piece kept it
  coherent; the typed layer and the proof grow level by level.
- **Representation is a relation** (`Ty.Rep`): a record is any object whose fields, read as JavaScript reads them,
  represent the record's fields, in any order and with extra fields; an optional's `none` is `undefined` and/or `null`
  as its type allows. The theorem quantifies over all JavaScript arguments representing the inputs
  (`ArgsRep`), so it covers callers that pass richer objects, omit optional arguments, or pass `undefined` explicitly.
- **Statements denote with three continuations** (normal, `break`, `continue`), still in continuation-passing style.
- **Narrowing replaces a variable's type in the context** (`Var.narrow`), keeping the environment aligned; a
  narrowing carries an embedding back into the wide type (`some`, union injection), used when control leaves the
  narrowed region.
- **A safety predicate** (Bool, mirroring the denotation) is in place for L2's numbers; trivially safe functions
  (no operation that can fault) get `fun _ => true` by definition, so their source theorems have no safety hypothesis.
- **Restrictions in L1:** `switch` over a union must list one case per variant in the union's order, each case but the
  last ending in `return`/`break`; a literal union compared with `===` must have distinct literals.
- **Frontend lesson:** variable references inside narrowed contexts cite named lemmas `ne.«x».«y»` instead of
  `by decide`; postponed tactic proofs block reducing `Var.narrow` during elaboration.
- **Proof size:** about 1,300 lines for L0 + L1 (L0 alone was about 300), most of it reusable: the relational
  environment, outcomes and continuations, narrowing.

### M3 notes

- **Numbers** denote `Int`. Arithmetic results must be safe integers (`inRange`); that is the first real safety
  condition. Comparisons and `===` are always safe. A negative literal `-5` is its own trivially safe form (`negNum`).
- **Arrays** denote lists, related elementwise (`Forall2`). `a[i]` is `T | undefined` (`listIndex`). Callbacks are arrow
  functions with an expression body, typed in the context extended with their parameter; the proof applies the
  callback's adequacy element by element (`someApply_conv` … `mapApply_conv`). `toSorted` denotes `sortedBy`: the
  model's stable insertion order over the comparator's sign matrix, so it agrees with any stable sort by a consistent
  comparator; its safety condition requires the comparator to be safe on every pair and consistent on the array.
- **Safety conditions are printed** as readable `«f».safe` definitions, and the source theorem of a function that is not
  trivially safe takes `(safe : «f».safe … = true)`. Conjuncts coming from trivially safe syntax are left out *by
  definition* (`andT` with static triviality flags, so the kernel drops them), so a condition mentions only operations
  that can leave the model: `total(a, b) = a + b * 2` has `inRange (b * 2) && inRange (a + b * 2)`;
  `scaled(xs, k)` has `List.all (List.filter … xs) (fun x => inRange (x * k))`. A structural condition would carry
  noise such as `if c then true else true` that the kernel cannot simplify. The proof takes `SafeSigs` (trivially safe
  callees are safe) for calls whose condition was left out.
- **Kernel lesson:** `inRange` is `Nat.ble n.natAbs (2^53 − 1)`. Stated with `Int` order, the kernel, unfolding it on a
  partly symbolic argument (`List.length es + 2`), recursed 2^53 deep in `Nat.sub`.
- **Elaboration lesson:** calls print their signature (`.call (s := sig.«f») …`); otherwise nested calls leave the
  callee's signature to unification through `?s.result` and elaboration fails.
- **Restrictions in L2:** callbacks take one parameter (comparators two), no index or array parameter; declared
  functions are not passed as values; indexing or `find` on an array of optionals is refused (a nested optional).
- **Tests:** `V2Tests/fixtures/l2.ts` (18 functions, checked in under 5 s), `Properties.lean` proves `scaled` safe on
  small inputs and transfers a property to every run, 24 negative fixtures. The differential test skips calls the model
  refuses (it makes no claim about them) and reports how many: 9,600 calls, 150 refused (overflows).
- **Proof size:** about 1,970 lines (+495 for L2: numbers about 110, arrays and callbacks about 300, the safety-flag
  refactor about 60, plus `Safe.lean`).

### M4 notes

- **Assignment** replaces the variable's component of the environment tuple (`Var.set`); the model's `assign` updates
  the innermost binding in place, so environments keep their length and the relation is preserved
  (`Var.assignRel`, 12 lines). Readable definitions print an assignment as a shadowing `let`.
- **Loops** denote through one combinator, `forIn items step exit` (a `foldr` building the continuation chain); the body
  runs with `K.map Prod.snd ⟨next, exit, next⟩`, so `break` is the loop's exit and `continue` the next iteration. One
  lemma, `conv_loop` (40 lines, induction over the iterations), serves `for…of` and `entries`; each statement case is
  about 30 lines. Nothing in the existing cases changed.
- **Readable loops** pass the environment tuple between iterations: `V2.forIn xs (fun x next exit s => let total :=
  s.1; …) (fun s => …) (total, xs, ())`, rebinding only the variables the text uses. `sum_eq` in `Properties.lean`
  proves `sum xs = xs.sum` by a plain induction over `forIn`.
- **Join points:** an `if` whose branches both complete now binds the rest of the list once (`let after' := fun s =>
  …`) instead of repeating it in each branch; repeated, sequential `if`s made readable text exponential.
- **Model change:** the iterations of `entries()` are named (`entryBindings`, via `zipIdx`), same meaning.
- **Tests:** `l3.ts` (12 functions, checked in about 6 s), 30 negative fixtures, differential 13,200 calls (292 refused,
  overflows).

## Checkpoint after M4: is adding constructs viable?

The design asked to compare the adequacy proof's size per construct and stop if it grew faster than linearly or a
level needed global invariants. Lines (`wc -l`, including comments and statements of lemmas):

| Level | Constructs | Proof | Typed syntax and denotation | Checker and printer |
| --- | --- | --- | --- | --- |
| L0 | bool, bigint, string, `const`, `if`, `return`, calls | 299 | 275 | 353 |
| L1 | records, spreads, unions, `switch`, optionals, narrowing | +1,175 | +638 | +550 |
| L2 | numbers with safety conditions, arrays, 7 methods, callbacks, sorting | +495 | +169 | +200 |
| L3 | `let`, assignment, two loops, `continue` | +179 | +55 | +81 |
| Total | | 2,148 | 1,137 | 1,184 |

Per construct, once the infrastructure exists:

- **An expression form** (an operator, a field read, `length`, indexing) costs 5 to 15 lines of proof, mostly a copy of
  its neighbour's case; the 22 binary-operator cases are near-identical.
- **A statement form without control flow** (`let`, assignment, `continue`) costs 5 to 20 lines.
- **A family that needs a new idea** costs one generic lemma plus short cases: callbacks (`*Apply_conv`, about 150
  lines for six methods), loops (`conv_loop`, 40 lines, plus 30 per loop form), sorting (sign matrix and `filterMap`
  over indices, about 40).
- **Infrastructure** was paid once, in L1: the relational representation, outcomes and continuations (`SRel`, `Exit`),
  narrowing. L2 needed one cross-cutting change (safety conditions that leave out trivially safe syntax, which added a
  `SafeSigs` hypothesis and touched every two-operand case mechanically); L3 needed none.

So the cost is linear, and the slope falls: L1 paid for the framework, L2 and L3 added constructs at a fraction of
the cost. No level needed a global invariant beyond the environment relation: assignment and loops fit the existing
outcome relation unchanged, which was the main risk named in the design (L3 is "the core of drive's code").

What did not scale as well, and what to do about it:

1. **Compile time of the general proof.** `Proof/Expr.lean` takes 51 s and `Proof/Safe.lean` 35 s (the rest of `V2`
   under 40 s together): structural recursion over `TExpr`, now 75 constructors, and its equation lemmas. It is paid
   once per build, not per file, but it grows with each constructor. Mitigation before L5: group operators into one
   constructor with an operator index (`arith op`, `cmp op`), which also removes most of the duplicated cases.
2. **Per-file checking hazards are in the untrusted printer, not the proof.** Three failures this round were all
   caught by the kernel and fixed in the printer or in kernel-friendly definitions: `inRange` stated with `Int` order
   made the kernel recurse 2^53 deep on a partly symbolic argument; nested calls needed their signature printed; a
   `switch` re-embedding needed a type ascription. Rule kept from v1: definitions the kernel unfolds must not recurse
   on large literals.
3. **Readable output** stays faithful but gets verbose for loops (the environment tuple and its rebinding). Join points
   keep it linear in the source. Users prove loop properties by induction over `forIn` (`sum_eq` is 8 lines).
4. **Safety conditions** are readable and only mention operations that can fault; the comparator condition
   (`consistent (signs …)`) is the one that is hard to discharge by hand and needs library lemmas (for example for
   comparators of the form `a.k - b.k` on safe integers) before drive's sorts are usable.
5. **Restrictions accepted so far** (each a candidate for a later level, none needed by the reference programs read so
   far): callbacks take one parameter, functions are not values, no counted `for`, no `while`.

**Conclusion: continue.** Adding constructs is viable: the theorem never changed shape, each level's proof was
additive, the marginal cost per construct is small and falling, and every per-file failure was caught by the kernel
in untrusted output. The next levels are the riskier ones the design already flagged: owned collections (L5) and
classes with backward functions (L6) change what an environment holds, so they will be the real test of the
environment relation. Plan changes from this checkpoint:

- L4 shrinks to "port drive's `trust.ts` and prove `Spec/Trust.lean`": integer-mode numbers moved into L2.
- Counted `for (let i = 0; i < n; i++)` moves to L7 with measured `while`: as a loop over `List.range` it needs the
  index not to be assigned in the body, a check that fits better with measured loops.
- Before L5: group operator constructors (point 1) and add comparator lemmas (point 4).

## Layout

| Path | Role | Trusted? |
| --- | --- | --- |
| `V2/Model/Syntax.lean` | Source AST (`Expr`, `Stmt`, `Function`, `Program`), `js` string literals | **Yes** |
| `V2/Model/Eval.lean` | Value-semantics evaluator, `Program.scoped`, `run`, `Converges` | **Yes** |
| `V2/Front/Convert.lean` | v1 parser AST → v2 AST (drops spans and annotations; refuses non-L0 forms) | **Yes** (with v1's lexer and parser) |
| `V2/Typed/Syntax.lean` | `Ty`, `Ctx`, `Var`, `Sig`, `FVar`, `TExpr`/`TArgs`/`TStmts`/`TProgram`, erasure, `returns` | No (checked) |
| `V2/Typed/Denote.lean` | Denotation, `TProgram.WF`, `TProgram.denote_cons` | No |
| `V2/Proof/Basic.lean`, `Array.lean`, `Safe.lean`, `Expr.lean`, `Stmt.lean`, `Trivial.lean` | Environment relation, representation and assignment lemmas, array and callback lemmas, adequacy of expressions and statements (with loops) | No |
| `V2/Proof/Adequacy.lean` | `V2.adequacy` (the general theorem) and `source_of` | No |
| `V2/Kernel.lean` | `kernel_rfl`: closed equations checked by the kernel only | No |
| `V2/Front/Check.lean` | Untrusted type checker and printer | No |
| `V2Main.lean` | CLI `ariadne2` (`translate`, `run`, `batch`, `signatures`) | `run`/`batch` are test oracles only |
| `V2Tests/` | Hand-written example, fixtures (`fixtures/*.ts` → `Generated/*.lean`), negative fixtures | — |
| `scripts/v2-check.sh` | Everything CI runs for v2 | — |

The statement of `V2.adequacy` and the definitions it mentions (`run`, `Converges`, `TProgram.erase`, `TProgram.WF`,
`Ty.encode`, `Ctx.encode`, the denotation) are what a reader must understand. The per-file source theorems
(`«f».source`) mention only `run`, `ast`, `Converges`, `JSValue` constructors and the readable definition.

## The theorem (L0)

```lean
theorem adequacy {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (xs : s.params.denote) :
    Converges (fun n => run P.erase n f (s.params.encode xs)) (.ok (s.result.encode (v.get P.denote xs)))
```

Proof structure (about 300 lines, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`; checked by
`scripts/V2Audit.lean` for every theorem in `V2` and `V2Tests`):

- `TExpr.adequate`/`TArgs.adequate`: mutual structural induction, under the hypothesis `FnsOK prog fs` (every function
  in scope converges to its denotation). Convergence is composed directly: take the maximum of the sub-runs' budgets
  plus one. No fuel-monotonicity lemma is needed.
- `TStmts.adequate`: induction on statement lists with the relation `StmtsRel` (a `return` carries the encoded result;
  falling through leaves the list's declarations on top of `Γ.toEnv ρ'` and the result is the continuation's).
- `TProgram.fnsOK`: induction over the program builds `FnsOK` for each prefix; `TProgram.lookups` shows the erased
  program's `find?` resolves each typed function (names are distinct).

Per file, the printer emits (all kernel-checked, nothing trusted):

```lean
def ast : Program := …                         -- the converted source
abbrev sigs : Sigs := …
def typed : TProgram sigs := …
theorem erased : typed.erase = ast := by kernel_rfl
theorem wf : typed.WF := by decide +kernel
def «f» (x : Int) … : Int := …                  -- readable definitions
theorem «f».body_eq : body.«f».denoteFn (earlier readable functions) = «f».uncurried := by kernel_rfl
theorem denote_eq : typed.denote = (readable functions) := TProgram.denote_cons … 
theorem «f».source (x : Int) … :
    Converges (fun fuel' => run ast fuel' "f" [.bigint x, …]) (.ok (.bigint («f» x …))) :=
  source_of erased wf denote_eq (… : FVar sigs "f" sig.«f») (x, …, ())
```

`V2Tests/Generated/L0.lean` is a complete example; `V2Tests/Hand.lean` shows a property proved on a readable
definition (`clamp_le`) that transfers to every run via `clamp_source`.

## Departures from the design, and why

1. **Statement lists denote in continuation-passing style**, not to a `Result` type (§7 of the design).
   `ss.denote fs k ρ` is the function's result when the list runs in `ρ` and `k` gives the result of what follows.
   With a `Result` type, the readable `if c then a else b` is not definitionally the denotation (a `match` on an
   `if` does not reduce), so the per-file `rfl` checks fail. CPS keeps them definitional. Revisit for loops (L3): a
   `for…of` in CPS is a fold whose step takes the loop's continuations; `break`/`continue` are continuations.
2. **Variables carry their name**: `Var Γ x τ` with `there : x ≠ y → …`, so a reference denotes the innermost binding of
   its name exactly as the evaluator's lookup does. The proofs are `by decide` in printed files.
3. **The model refuses shadowing** (`Program.scoped`, checked by `run` before calling). JavaScript resolves names
   lexically with block-scoped `const` and a temporal dead zone; the evaluator resolves variables in a dynamic
   environment and functions in the program. These agree when no declaration (parameter or `const`) reuses a name in
   scope or a function's name, and function names are distinct. Under that condition, reading a name before its
   declaration is a `referenceError` in the model and a `ReferenceError` (TDZ) in JavaScript. `TProgram.WF` includes
   `P.erase.scoped`, so the theorem covers it; the checker reports `A2004` early.
4. **Calls are checked semantically**: `FnsOK prog fs` replaces a syntactic program-prefix relation; it composes
   cleanly with induction over the program and will carry over to recursion (L7) as a fixed-point hypothesis.
5. **`Ty` is `bool | int | string` at L0**; `int` is `bigint` (exact `Int`). Integer-mode `number` and the other types
   arrive with their levels.
6. **Checked output is built from the readable definitions** (`body_eq`, `denote_eq`), so no per-file check unfolds a
   callee. See the measurements: checking `«f» = denotation` directly re-checks every callee and grows exponentially
   with call depth when a call's result is used more than once (zeta-reduction duplicates it).

## Trusted base (L0)

- Lean's kernel, and the statement of `V2.adequacy` with the definitions it mentions.
- `V2/Model/*`: that `run` agrees with JavaScript on every program for which it returns `.ok` (tested by
  `scripts/v2-differential.mjs`: every exported fixture function on random and edge inputs, Node vs `ariadne2 batch`;
  a mutation of string `<=` in the model is caught).
- v1's lexer and parser plus `V2/Front/Convert.lean`, and the printer's rendering of `ast` (that the printed `ast` is
  the parse of the file).
- Not trusted: the type checker, the printer's typed term, readable definitions and proofs (all re-checked by the
  kernel).

## Measurements (M0)

Synthetic L0 files of `n` chained functions (each 14 lines: arithmetic, a call to the previous function, string
comparisons, nested `if`/`else if`, `?:`), checked with `lake env lean` on the development container. trust.ts is about
the size of `n = 25`.

| Version | n = 25 (375 lines) | n = 50 (750) | n = 100 (1500) |
| --- | --- | --- | --- |
| `rfl` for `«f» = denotation` | > 400 s, 4.5 GB, heartbeat timeouts | — | — |
| Modular `body_eq` with `rfl` | 76 s, 0.75 GB | — | — |
| `body_eq` by `kernel_rfl` | 10.6 s, 1.8 GB | 34 s, 2.4 GB | 164 s, 4.4 GB |
| + `erased` by `kernel_rfl`, `wf` by `decide +kernel`, `source_of` | **8.7 s, 1.8 GB** | 26 s, 2.4 GB | 116 s, 4.3 GB |

Breakdown at n = 50 (seconds, cumulative cut points): AST and typed bodies about 5; `wf` about 7 (of which
`scoped` about 6, `names.Nodup` about 2); readable definitions about 1.5; `body_eq` about 2.4; source theorems
about 6.

Remaining superlinear terms, with mitigations if larger files need them:

- `scoped` and `Nodup` compare names pairwise with kernel string equality (quadratic in the number of names). Options:
  check per function against a sorted name list, or compare interned indices with a checked name table.
- Each source theorem resolves an `FVar` path of length up to `n` (quadratic overall). Options: state source theorems
  through the readable tuple's projections, or batch them.

## How to run

```sh
lake build V2 ariadne2
.lake/build/bin/ariadne2 translate file.ts --out File.lean --namespace My.File
.lake/build/bin/ariadne2 run file.ts f 3n '"text"' true
scripts/v2-check.sh      # everything CI runs for v2
```

## Next steps

- M2 (L1): readonly records and unions, `switch` with narrowing, optionals. Start with `Ty.record`/`Ty.union` denoting
  products and sums, field reads, `== null`. Integer-mode `number` (with the −0 relation) can be its own small level
  before or after L1; drive needs it.
- Keep `V2.adequacy` the single theorem; extend `TExpr`/`TStmts` and add cases. Watch the proof size per construct
  (design §11 checkpoint).

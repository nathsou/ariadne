# Ariadne v2: progress

Companion to [V2-DESIGN.md](V2-DESIGN.md). Records what exists, where the implementation departs from the design and
why, and measurements. Update it with each milestone.

## Status

| Milestone | State |
| --- | --- |
| M0: measurements, CI | Kernel-cost measurements below. CI job `v2` runs `scripts/v2-check.sh` and is part of the required `verify` status. |
| M1: L0 end to end | Done: model, typed syntax, erasure, denotation, general theorem, frontend, CLI, fixture, differential and negative tests. |
| M2: L1 | Done: records (literals, `{ ...r, f }`, field reads), string-literal unions, tagged unions (string or boolean tags) with `switch` narrowing, optionals (`?:`, `T \| null`, `T \| null \| undefined`), `== null` narrowing in expressions and statements, `??`, optional parameters, `break` in `switch`. Theorem, frontend, fixture, differential and negative tests. |
| M3 (L2), M4 (L3) | In progress (the model already covers them; see below). |

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

## Layout

| Path | Role | Trusted? |
| --- | --- | --- |
| `V2/Model/Syntax.lean` | Source AST (`Expr`, `Stmt`, `Function`, `Program`), `js` string literals | **Yes** |
| `V2/Model/Eval.lean` | Value-semantics evaluator, `Program.scoped`, `run`, `Converges` | **Yes** |
| `V2/Front/Convert.lean` | v1 parser AST → v2 AST (drops spans and annotations; refuses non-L0 forms) | **Yes** (with v1's lexer and parser) |
| `V2/Typed/Syntax.lean` | `Ty`, `Ctx`, `Var`, `Sig`, `FVar`, `TExpr`/`TArgs`/`TStmts`/`TProgram`, erasure, `returns` | No (checked) |
| `V2/Typed/Denote.lean` | Denotation, `TProgram.WF`, `TProgram.denote_cons` | No |
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

# Design

Ariadne translates a TypeScript subset into readable Lean definitions and proves, once and for every
accepted program, that the TypeScript computes what the definitions compute. This document explains
how: the trusted model of JavaScript, the typed syntax, the denotation, the theorem, the checks made
per file, and how the pieces are tested. [LANGUAGE.md](LANGUAGE.md) lists the accepted subset.

## Principles

1. **A value semantics as the trusted model.** In a language with no visible in-place mutation and no
   identity comparison of objects, JavaScript's reference semantics coincides with a value semantics.
   The model is a big-step, fuel-indexed evaluator over plain JavaScript values, executable so it can
   be tested against a JavaScript engine. The one place objects change in place, a class's `Map`
   fields, has a second model that changes them in place, proved equal to the value model.
2. **The typed program is the source plus types.** The type checker builds an intrinsically typed
   syntax tree whose erasure is exactly the parsed tree: one typed constructor per source form, no
   desugaring. The checker is untrusted; the kernel checks `typed.erase = ast`.
3. **A compositional denotation directly on typed syntax.** Statements, loops, `break`, `continue` and
   early `return` denote through continuations, so the source's control flow needs no rewriting.
4. **One theorem by induction on typed syntax.** Each construct adds one case to one proof; there are
   no per-program proofs and no generated tactic scripts.
5. **Readable output, checked by the kernel.** The printed Lean definitions are checked equal to the
   denotation per file. The printer is untrusted.
6. **Nothing expensive in the kernel per file.** Per-file kernel work is structural: erasure, a static
   check, and definitional equalities. The kernel never runs the lexer, parser or checker.

## Architecture

```
file.ts ──parse, convert (trusted)──▶ ast : Program              (the model's syntax)
                                          │
                       typecheck (untrusted)
                                          ▼
                                   typed : TProgram               (erase typed = ast)
                                          │
                  print (untrusted)       │ denote (defined once, in Lean)
                                          ▼
                       Out.lean: readable defs ══ kernel ══ typed.denote

Proved once:    ∀ typed, well formed, safe → run (erase typed) converges to a value representing denote typed
Checked per file (kernel):  erase typed = ast,  well formed,  readable defs = denoteRS typed
                            (proved once: denoteRS, over the file's structures and inductives, is denote)
Concluded per file:          every readable def is what the TypeScript function computes (in the model)
```

| Path | Role | Trusted |
| --- | --- | --- |
| `Ariadne/Parse/*` | Lexer and parser for the TypeScript subset, with diagnostics | **Yes** |
| `Ariadne/Front/Convert.lean` | Parsed syntax → the model's syntax (drops spans and annotations, refuses other forms) | **Yes** |
| `Ariadne/Model/Syntax.lean` | The model's syntax (`Expr`, `Stmt`, `Function`, `Program`), `js` string literals | **Yes** |
| `Ariadne/Model/Eval.lean` | Value-semantics evaluator, static scoping check `Program.scoped`, `run`, `Converges` | **Yes** |
| `Ariadne/Model/Store.lean` | Store model of classes (`runMethodStore`) | **Yes** |
| `Ariadne/Typed/*` | Types, typed syntax, erasure, denotation, safety conditions, well-formedness | No |
| `Ariadne/Eqns/*` | Equation lemmas of the typed syntax's large definitions (see Build time) | No |
| `Ariadne/Proof/*` | The adequacy proof, the store model's agreement with the value model, frames (which fields a method leaves), and the idiomatic denotations' equality with the denotation (`Direct`, `Idiom`, `Named`) | No |
| `Ariadne/Lib/*` | Lemmas for proofs about readable definitions: loops (invariants, folds), maps, string order, `toSorted` (its consistency conditions, what it returns, and `cmp_laws` for comparators), the `readable` simp set | No |
| `Ariadne/Kernel.lean` | `kernel_rfl`: closed equations checked by the kernel alone | No |
| `Ariadne/Audit.lean`, `Audit.lean` | The soundness gate, and its configuration for Ariadne (`trusted.lock`) | No |
| `Ariadne/Front/Check.lean` | Type checker and printer | No |
| `Main.lean` | The `ariadne` command (`translate`, and the test oracles `batch` and `signatures`) | No |
| `Tests/` | Fixtures and their generated files, model cases, negative fixtures, property proofs | — |

## The model

### Values, evaluation and faults

```lean
inductive JSValue where
  | undefined | null | bool (b : Bool) | number (n : Int) | bigint (n : Int) | string (s : JSString)
  | record (fields : List (String × JSValue)) | array (elems : List JSValue)
  | closure (params : List String) (body : Expr) (env : List (String × JSValue))
  | function (name : String) | map (kvs : List (JSString × JSValue))
```

- `JSString` is `List UInt16` (UTF-16 code units); `<` is code-unit order.
- `evalExpr`, `execStmts`, `loop` and `call` take fuel; every recursive call consumes it, and every
  definition is structurally recursive on it, so the evaluator runs compiled (for tests) and reduces
  in the kernel. `Converges f v := ∃ n, ∀ m ≥ n, f m = v`.
- Statements return an `Outcome`: `normal env`, `returned v env`, `broke env`, `continued env`.
- **Faults make no claim.** The model faults (`unsupported`, `typeError`, `referenceError`, `timeout`)
  wherever the subset leaves JavaScript's behaviour unmodelled: coercions between types, `===` between
  objects, prototype properties, numbers outside the safe-integer range, inconsistent comparators. The
  claim tested against JavaScript is: whenever `run` returns `.ok v`, JavaScript returns a value with
  the same observation.

### Names

The environment is an association list, innermost binding first. JavaScript resolves names lexically
(block-scoped `const`, a temporal dead zone); the model resolves them dynamically. The two agree when
no declaration reuses a name in scope or a function's name, so the model refuses shadowing: the static
check `Program.scoped` (run by `run` before calling) requires distinct names, assignments only to
`let`s and parameters, loop variables never assigned, `this` only in its dedicated forms, and methods
called inside expressions that change no state. Reading a name before its declaration is then a
`referenceError` in the model and a `ReferenceError` in JavaScript.

### Numbers

`number` denotes `Int` restricted to ±(2^53 − 1), where binary64 arithmetic is exact. `+`, `-`, `*`
and negation fault outside that range. `%` is exact on integers (truncated, with the dividend's sign)
and faults on a zero divisor. `/` on numbers gives fractions, so only `Math.floor(a / b)` is accepted, as
one form (`floorDiv`): on safe integers the quotient's rounding error is below `|a| / |b| · 2^-53`, less
than `1 / |b|`, the distance from a non-integer quotient to the nearest integer, so rounding never
crosses an integer and the result is floor division (`Int.fdiv`). The model faults on a zero divisor or
an unsafe operand. The frontend refuses `**`, bitwise operators and literals that are not safe
integers. Negative zero is not distinguished from zero: within the subset (no `Object.is`, no division
whose result is a fraction) the two cannot be told apart. `bigint` denotes `Int` exactly; its `/`
truncates (`Int.tdiv`) and `%` is `Int.tmod`, faulting on a zero divisor (JavaScript throws).

### Strings

Strings are lists of UTF-16 code units. `startsWith`, `endsWith`, `includes` and `indexOf` take a string;
`slice` takes one or two integers, counted from the end when negative and clamped to the string. All
are total.

### `while` loops

`while (c) body` runs as `loop` over iterations that bind nothing, each starting with
`if (!c) break;`. Like a counted loop, the model builds no more iterations than its fuel, so a loop
that does not end is a timeout. The store model runs the same iterations through `sLoop`, so its
agreement with the value model is the loop case already proved.

### Records, optionals and arrays

A record is any object whose fields, read as JavaScript reads them, represent the record's fields, in
any order and with extra fields. An optional's `none` is `undefined` or `null`, as its type allows.
Arrays are lists. Callbacks are closures over a snapshot of the environment, which equals capture by
reference because callbacks have expression bodies and cannot assign. `toSorted` is a stable insertion
by the comparator's sign matrix, so it agrees with any stable sort by a consistent comparator.

### Classes: value model and store model

A class's state is a record of `Map` fields. In the value model the object a method runs on is the
binding `this`; a method called as a statement gets a copy and the caller takes the copy it leaves.
`this` is never a value, so no map is ever shared.

The store model (`Model/Store.lean`) is closer to JavaScript: the object's state is one store threaded
through statements, `this.f.set/delete` change it, and a method called as a statement runs on the same
store. `runMethod_store` proves the two models equal for every program that passes `Program.scoped`;
`scoped_pure_keeps` proves that a method an expression may call returns the store it was given, so
evaluating expressions without threading the store is exact.

## Typed syntax

```lean
inductive Ty where
  | bool | int | number | string                -- `int` is bigint
  | tag (t : TagLit) | lits (first : JSString) (rest : List JSString)   -- literal types and unions
  | option (n : Nullish) (τ : Ty) | record (fs : Fields) | union (key : String) (vs : Variants)
  | array (τ : Ty) | map (τ : Ty)
inductive TExpr (Φ : Sigs) : Ctx → Ty → Type   -- one constructor per source expression form
inductive TStmts (Φ : Sigs) : Ctx → Ty → Type  -- statement lists; declarations extend the context
```

- **Variables carry their name**: `Var Γ x τ` with `there : x ≠ y → …`, so a reference denotes the
  innermost binding of its name exactly as the evaluator's lookup does. Printed files cite named
  lemmas `ne.«x».«y»` for the inequalities.
- **Narrowing** (`switch` on a tag, `== null`) replaces a variable's type in the context and carries an
  embedding back into the wide type for when control leaves the narrowed region.
- **Callbacks** are their own syntax: `TFn` (an arrow of zero or one parameter, or a declared
  function) and `TCmp` (a two-parameter comparator).
- **`switch`** takes a list of arms (`TArms`): cases in any order, grouped labels, `default`,
  fall-through.
- **Binary operators** are one constructor indexed by an operator (`TExpr.bin (op : Op σ τ)`); string
  methods taking a string are one constructor indexed by the method (`TExpr.smethod`).
- **`while`** (`TStmts.whileLoop`) needs a trivially safe condition, so a loop's safety is that of its
  iterations and that it ends.
- **Well-formedness** is a decidable predicate the kernel checks per file: `bodiesOk` (every path
  returns; no stray `break`/`continue`; state changes only in `void` methods) and the model's own
  `Program.scoped` on the parsed program, which also requires distinct names.

## Denotation and safety

- `Ty.denote` maps types to Lean types (`Int`, `Bool`, `JSString`, `Option`, `List`, products for
  records, sums for unions, association lists for maps).
- Statement lists denote in continuation-passing style: `ss.denote fs k ρ` is the function's result
  when the list runs in `ρ`, with continuations for falling through, `break` and `continue`. This keeps
  the readable `if c then a else b` definitionally equal to the denotation.
- Loops denote through one combinator, `forIn items step exit` (a `foldr` building the continuation
  chain). Counted loops iterate over `range n`.
- The readable definitions are not compared with `denote` directly but with a denotation closer to the
  printed Lean, proven equal to it once, for every program. This is how the output gets more idiomatic
  without trusting the printer; there are three such steps, each a definition and one theorem:
  - **Folds** (`TStmts.denoteD`, `Ariadne/Typed/Direct.lean`; `TStmts.denoteFn_eq`,
    `Ariadne/Proof/Direct.lean`). The result type is any `R` (a `return` gives `r v`), and a loop whose
    body has no `return` anywhere and no `break` of its own is a fold,
    `rest (items.foldl (fun ρ y => body (y, ρ)) ρ)`. The proof: the continuation-passing denotation is
    natural in its result type (`denoteD_nat`), a body without `return` ignores `r` and one without
    `break` ignores the break continuation, and `forIn` with a step that always continues is a fold.
  - **States** (`TStmts.denoteR`, `Ariadne/Typed/Idiom.lean`; `TStmts.denoteFn_eq_R`,
    `Ariadne/Proof/Idiom.lean`). A loop, or an `if` or `switch` whose branches all go on after it,
    carries only the variables it assigns (`TStmts.writes`), as a flat tuple, and a branch that cannot
    `return`, `break` or `continue` gives that tuple as its value (`let (a, b) := if c then … else …`).
    The proof is a frame theorem (`denoteD_frame`): a statement calls its continuations only on
    environments that agree with its own outside what it writes.
  - **Named types** (`TStmts.denoteRS`, `Ariadne/Typed/Named.lean`; `TStmts.denoteFn_eq_S`,
    `Ariadne/Proof/Named.lean`). Types denote through a file's `names : Names` (`Ty.den`): a record or
    union listed there is the Lean type given with it, a structure or an inductive, and `isos : Isos names`
    says how its values correspond to the record's fields or the union's variants (`view`, `make`, case
    analysis, with the laws that make them inverse). The proof is a logical relation: `Ty.conv` maps a
    value of the file's types to the denotation's, and every expression, statement and safety condition
    commutes with it (`TExpr.conv_denS`, `TStmts.denoteRS_conv`, `TStmts.safeS_eq`). The general
    theorem's conclusions carry over through `Ty.RepS`, representation over the file's types, which is
    `Ty.Rep` after `Ty.conv` (`Ty.repS_eq`).

  The adequacy proof stays about `denote`.
- A `while` loop denotes `whileDo cond step exit`: up to `loopBound` (2^64) iterations, leaving after
  that. Its safety condition, `whileSafe`, says that it ends within them, each iteration safe, so
  termination is a proof obligation, met with a measure (`whileSafe_of_measure`). `whileDo` and
  `whileSafe` carry the kernel's lowest unfolding priority: comparing a readable definition with the
  denotation, the kernel unfolds the side with the greater definitional height first, and the
  denotation reaches the loop through `&&` and other small definitions; with an ordinary height, it
  would unroll the readable side's loop instead, through `loopBound` iterations.
- The denotation is total. Where JavaScript can fault, a separate **safety condition** (computed from
  the same syntax) says that no fault occurs. Conjuncts from syntax that cannot fault are left out by
  definition, so a printed condition mentions only operations that can leave the model, for example
  `inRange (b * 2) && inRange (a + b * 2)`. Functions with no such operation are trivially safe, and
  their source theorems have no safety hypothesis.
- A `void` method denotes the state it leaves.

## The theorem

```lean
theorem adequacy (P : TProgram Φ) (wf : P.WF) (v : FVar Φ f s) (hv : s.void = false) (xs : s.params.denote)
    (vs : List JSValue) (args : ArgsRep s.params vs xs) (safe : v.safe P.safety xs = true) :
    ∃ w, Converges (fun n => run P.erase n f vs) (.ok w) ∧ s.result.Rep w (v.get P.denote xs)
```

`Ty.Rep` relates JavaScript values to denoted values, and `ArgsRep` lists of arguments to inputs, so
the theorem covers every caller whose arguments represent the inputs (richer records, omitted optional
arguments, explicit `undefined`). `adequacy_state` is the same statement for a `void` method, about the
state it leaves, and `adequacy_state_store` restates it for the store model.

Proof structure (`Ariadne/Proof`):

- `FnsOK prog fs`: every function in scope converges to its denotation. `TProgram.fnsOK` builds it by
  induction over the program; calls in the proof use it.
- Expressions: mutual structural induction (`TExpr.adequate`). Convergence is composed directly: the
  maximum of the sub-runs' fuel, plus one. One lemma per operator family (`Op.sound`) and per callback
  kind (`TFn.adequate`, `TCmp.adequate`).
- Statements: an environment relation (`EnvRel`) and an outcome relation (`SRel`), with one generic
  loop lemma (`conv_loop`) and one for `switch` arms (`TArms.adequate`).
- Store model: induction on fuel over statements, loops and method calls together, with the invariants
  that the environment binds `this` at most once and that no statement binds or assigns it; one lemma
  per statement form (`agree_*`).

## What a translated file contains

```lean
noncomputable def ast : Program := …            -- the converted source
noncomputable def typed : TProgram sigs := …
theorem erased : typed.erase = ast := by kernel_rfl
theorem bodies_ok : typed.bodiesOk = true := by decide +kernel
theorem ast_scoped : ast.scoped = true := by decide +kernel
theorem wf : typed.WF := TProgram.wf_of typed erased bodies_ok ast_scoped
def f (x : Int) … : Int := …                   -- readable definitions
def f.safe (x : Int) … : Bool := …             -- safety conditions (when not trivial)
structure Item where …                         -- the source's types, as Lean declarations
inductive Shape where …
noncomputable def names : Names := …            -- the records and unions they are
noncomputable def isos : Isos names := …        -- how their values correspond
def f.loop … := …                              -- loop bodies
def f (x : Int) … : Int := …                   -- readable definitions
def f.safe (x : Int) … : Bool := …             -- safety conditions (when not trivial)
theorem f.body_eq : body.f.denoteRSFn names isos (earlier readable functions) = f.uncurried := by kernel_rfl
theorem denote_eq : typed.denote = Sigs.canon names isos sigs (readable functions) := TProgram.denote_consS …
theorem f.source (x : Int) … (vs : List JSValue) (args : ArgsRepS names isos …) (safe : f.safe x … = true) :
    ∃ w, Converges (fun fuel => run ast fuel "f" vs) (.ok w) ∧ Ty.RepS names isos … w (f x …) := …
```

The source's named types become Lean declarations, so that the definitions and statements about them
read like the TypeScript:
- a record, a structure (`structure Floor where written : Int …`), read by name (`fl.seed`), built with
  its constructor (`Candidate.mk index committed …`) and updated with `{ a with name := n }`;
- a union of records, an inductive with a constructor per variant (`CopyFact.damaged`,
  `Choice.true order`, `CopyFact.opened f`); a variant with more than one field takes a structure,
  `CopyFact.Variant.opened`, or the source's own name for it when the variant is a named interface;
- a variant record anywhere is its payload, the fields after the tag: nothing (`Unit`), its one field,
  or that structure;
- a literal union, `Fin n`, with a constant per literal (`Commit.bad`), and any other named type an
  abbreviation of the Lean type it denotes.

A record whose field takes a name Lean derives for a structure (`mk`, `rec`, …), or a union whose tag
cannot name a constructor, stays a product or a sum, with accessors (`@[reducible, readable]`, so
`simp [readable]` unfolds them). Types without a name are products, sums and lists.

`names` lists which records and unions are which declarations, and `isos` gives, per declaration, the
view as fields or variants and back, with the laws, proved by `rfl` and case analysis. Both are generated:
reading a source theorem about a structure means reading `isos` as the field-by-field correspondence it
prints, as the type abbreviations `ty.T` are read as the source's types.

The readable definitions use these names: fields are read by name, a `switch` is a `match` on the
inductive's constructors that binds the narrowed variable to its payload, a loop's body is a named
definition (`f.loop`, or `f.loop1`, `f.loop2`, …) taking the variables it reads, and a loop's or a
branch's state holds only what it assigns. A loop that never returns or breaks is
`Ariadne.fold init items f.loop`; others are `forIn` with `next` and `exit`. All of it is definitionally
`denoteRS`, which is what the per-file `body_eq` checks.

A class's file also says which fields each method leaves alone:

```lean
theorem frames.marks : typed.frames "marks" = [false, true, …] := by decide +kernel
theorem pack.keeps.marks (this : Registers) … : (pack this …).marks = this.marks :=
  frame_of_fnS isos … denote_eq frames.marks … (f := pack.uncurried) rfl (acc := fun r => r.marks) …
```

`TProgram.frames g` marks a method that neither sets nor deletes in `this.g` and calls only marked
methods; it is a syntactic check over the typed program, evaluated by the kernel. `TProgram.frame`
(`Ariadne/Proof/Frame.lean`) proves once that a marked method returns a state with the same `g`: over
any run of its body, every variable named `this` keeps `g`'s value, through loops, `switch` and the
methods it calls. The translator predicts the marks to know which lemmas to write; a wrong prediction
fails `frames.g`, never a lemma.

Each `body_eq` compares one function's denotation with its readable definition, with callees taken as
the earlier readable definitions, so no check unfolds a callee. The source theorems mention only `run`,
`ast`, `Converges`, `Ty.RepS` (with `names` and `isos`) and the readable definitions. `Tests/Properties.lean`,
`Tests/TrustSpec.lean`, `Tests/RegistersSpec.lean` and `Tests/TreeSpec.lean` prove properties of
readable definitions and transfer them to every run.

## Testing

- **Model validation** (`scripts/model.mjs`, `Tests/model`): hand-written cases run in Bun and in the
  model; every `t_*` function must agree, every `fault_*` function must be refused.
- **Differential** (`scripts/differential.mjs`): every exported function of every fixture on random
  and edge inputs, including records with extra fields in any order, omitted optional arguments, and
  objects with random `Map` states for methods (46,800 calls). Calls the model refuses are counted and
  make no claim.
- **Model fuzzing** (`scripts/fuzz-model.mjs`): random programs, generated by type so that most run to a
  value (arithmetic near the safe-integer limits, strings with surrogates, arrays and their callbacks,
  records, `switch`, loops with `break` and `continue`), run in Bun and in the model. Wherever the model
  gives a value, JavaScript must give the same one.
- **Parser cross-check** (`scripts/crosscheck.mjs`): an independent converter from the TypeScript
  compiler's syntax tree to the model's syntax, following the mapping documented in
  `Ariadne/Front/Convert.lean`. For every test file, and for random expressions dense in operators,
  parentheses, literals and escapes, the program Ariadne's parser and converter produce (`ariadne ast`)
  must be the one the compiler's tree gives; and Ariadne must refuse what the compiler finds a syntax
  error.
- **Validators** (`scripts/validators.mjs`): the guards `ariadne validators` prints accept every argument
  list the differential test draws; on mutated ones (wrong types, fractions, numbers beyond the safe
  integers, holes, getters, class instances, non-string map keys) JavaScript and the model must agree
  wherever a guard accepts, and the model must be able to represent what it accepts.
- **Regeneration**: each fixture's generated file must regenerate with no diff and kernel-check.
- **Negative fixtures** (`scripts/negative.mjs`, `Tests/negative`): every refusal, with its diagnostic
  code.
- **Audit** (`lake exe audit`, `Ariadne/Audit.lean`):
  - every declaration is replayed through the kernel;
  - every theorem uses only `propext`, `Classical.choice` and `Quot.sound` (`sorry` and `native_decide`
    would show up as axioms);
  - nothing theorems depend on is `partial`, `unsafe`, `implemented_by` or `extern`, so the compiled
    evaluator the differential tests run is the one the proofs reason about;
  - `trusted.lock` matches. It records the statements of the public theorems, and the definitions of
    `run`, `runMethod`, `runMethodStore`, `Converges`, `Ty.Rep` and `ArgsRep` with everything they use:
    bodies when short, fingerprints for recursive and derived definitions. A change to the trusted base
    is a change to that file.
- **CI** (`scripts/check.sh`): pinned tools and no build cache, since Lean imports compiled modules
  without re-checking their proofs.

## Cost

- The proof is about 3,700 lines (`Ariadne/Proof`). Once the framework existed, an expression form cost
  5 to 15 lines, a statement form 5 to 20, and a family needing a new idea one generic lemma plus short
  cases (callbacks, loops, sorting, `switch` arms). The theorem's statement never changed shape.
- The idiomatic denotations add about 1,400 lines of definitions (`Ariadne/Typed/{Direct,Idiom,Named}`)
  and 3,100 of proofs (`Ariadne/Proof/{Direct,Idiom,Named}`), the named types most of them: every value
  operation, expression, statement and safety condition needs its case of the commutation lemmas. A file
  pays nothing for them: its checks compare the readable definitions with one denotation, as before.
- A clean `scripts/check.sh` takes about 3 minutes on 4 cores. Generated files check in 5 to 40 s
  (drive's `registers.ts`, 429 lines and 30 methods, is the largest).
- Lean derives a recursive definition's equation lemmas the first time a proof unfolds it, in that
  proof's module. For `TExpr.denote` and its neighbours this takes seconds each, so `Ariadne/Eqns/*`
  derive them in modules that build in parallel, and the proofs import them.
- Remaining superlinear terms per file: the static check compares names pairwise, and each source
  theorem resolves a function index of length up to the number of functions.

## Why the kernel does not run the parser

The parser and converter are trusted as compiled code: `ast` in a generated file is what the `ariadne`
binary produced, not a theorem about the source text. Asking the kernel to check
`Parse.parse source >>= convertProgram = .ok ast` was measured (Lean 4.35, `kernel_rfl`) and is not
practical:

| Input | Kernel time |
| --- | --- |
| lexing `basics.ts` (1.3 KB) | about 4 s |
| parsing the first 98, 218 and 345 characters of `basics.ts` | 4 s, 13 s, 30 s |
| parsing its first 643 characters | out of memory (8 GB) |
| a loop of `peek`, `accept` and `identifier` over 200 and 400 tokens | 6 s, 18 s |

The cost is in the parser's monadic style (state threaded through `StateT` over `Except`), which the
kernel's call-by-need reduction evaluates in quadratic time with large intermediate terms; neither the
token array (a list of remaining tokens costs the same) nor string comparisons are the cause. Drive's
kernel files are 11 to 14 KB.

What would work is a certificate the kernel checks rather than a computation it replays: the translator
emits the tokens and a lossless parse tree (keeping parentheses and the source's forms), and the kernel
checks that lexing the source gives the tokens, that printing the tree gives them back (a structural
recursion, with precedence checked where a child has no parentheses), and that converting the tree gives
`ast`. The printer would replace the parser in the trusted base, and be cross-checked against the
TypeScript compiler as the parser is now. Until then, the trust in the front end rests on that
cross-check (`scripts/crosscheck.mjs`), and on the regeneration check in CI.

## Practical rules

- Anything the kernel must reduce must be structurally recursive, and must not recurse on large
  literals: `inRange` is `Nat.ble n.natAbs (2^53 − 1)`, since an `Int`-order statement made the kernel
  recurse 2^53 deep on a partly symbolic argument.
- An eliminator the kernel reduces must match the value separately from its structural argument;
  printed terms carry their types, since a metavariable left by elaboration blocks kernel reduction.
- Never `decide` a property whose evaluation runs a program on large inputs.
- Readable output stays linear in the source: an `if` whose branches both continue binds the rest of
  the list once (a join point) instead of repeating it.

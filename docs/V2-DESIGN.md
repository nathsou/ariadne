# Ariadne v2: a TypeScript subset to Lean translator with a general correctness theorem

This document is a self-contained brief for rebuilding Ariadne from scratch. It explains the end goal, what exists today
and why it is being replaced, the architecture of the rebuild, the one theorem everything is organised around, the order
in which language features are added, and how to run the work. A new contributor (human or agent) should be able to
start from this file alone.

## 1. Goal

A translator from a subset of TypeScript to readable Lean 4 definitions, together with **one general theorem, proved once
in Lean**, saying that for every program the translator accepts, the TypeScript code (as modelled by a small, executable,
trusted semantics of JavaScript) computes exactly what the generated Lean definitions compute. Users then prove
properties of the Lean definitions, and those properties transfer to the TypeScript code with no per-program proof work.

The motivating user is the verified kernel of [nathsou/drive](https://github.com/nathsou/drive) (`core/kernel/trust.ts`,
`registers.ts`, `tree.ts`; see its `docs/VERIFIED_KERNEL.md`). Drive today has its own pipeline: an untrusted translator
to Lean `do` code, a round trip back to TypeScript, and differential tests, with the JavaScript prelude, the
printer's correspondence table and Lean's `do` elaborator trusted. The rebuild should be able to take drive's kernel
(after modest rewrites) and prove drive's existing specifications against definitions whose correspondence to the
TypeScript is a theorem, not a convention.

**Success criterion for the whole project:** drive's `trust.ts`, then `registers.ts` and `tree.ts`, translate with the
general theorem covering them, and the statements in drive's `verify/Drive/Spec/Trust.lean` (and later
`Registers.lean`) are proved about the generated definitions and transferred to the TypeScript.

## 2. Background: what exists and why it is being replaced

### 2.1 Ariadne v1 (this repository)

Ariadne v1 lives on `main` (operational semantics and a scalar compiler) and on the branch
`claude/design-certified-shallow-translation` ([nathsou/ariadne#4](https://github.com/nathsou/ariadne/pull/4), a draft
PR, about 82,000 added lines). This design branch starts from that branch's head, so all of v1 is in the tree for
reference and reuse. Its main pieces:

- **Frontend:** a lexer, parser and checker for a TypeScript subset (`Ariadne/Lexer.lean`, `Parser.lean`, `Check.lean`,
  with ownership rules for borrows, moves and owned fields). Per file, the kernel checks the lexing, parsing and checking
  equations (`kernel_rfl` over the whole frontend run).
- **Trusted model:** a **heap-based** fuel-indexed evaluator `Ariadne/Semantics.lean` (cells for locals, objects on a
  heap, closures), with fuel monotonicity and convergence (`Fuel.lean`, `Convergence.lean`).
- **Shallow translation:** an elaborator (`Ariadne/Shallow/Elaborate.lean`, about 1,350 lines) from source syntax to an
  intrinsically typed Core (`Shallow/Core.lean`), a denotation (`Shallow/Denote.lean`), a printer
  (`Shallow/Emit*.lean`) and per-file kernel checks that the elaborator produced the printed Core and that the printed
  Lean definitions equal the denotation. The elaborator rewrites heavily before and during translation: continuations
  for joins, loop-control rewriting of `return`/`break`/`continue`, state threading for mutated parameters
  (`StatePlan`), class lowering (`ClassPlan`), throw lowering, projections.
- **Adequacy:** a value-erasure lemma relating a guard semantics to the denotation for every Core term
  (`Shallow/Safety/Erasure/*`), operational adequacy for small fragments (scalars, guarded Int53, data reads), a
  budget-free weakest-precondition library over the heap evaluator (`Shallow/Adequacy/WP*.lean`), three reference
  programs (registers, a decision function, a tree) proved by hand against the evaluator (`Examples/ReferenceSource`,
  about 2,600 lines), and generated per-function source theorems for straight-line functions over scalars, scalar arrays
  and records of scalars.

### 2.2 Why v1's general theorem is out of reach

The general fundamental lemma (elaboration then denotation agrees with the evaluator for every accepted program) was
never proved, and assessing it led to this rebuild. The obstacles are structural:

1. **The trusted model is a heap evaluator.** Every theorem relates heap objects to Lean values, which drags in
   aliasing, footprints and soundness of the ownership checker even for code that never mutates anything.
2. **The elaborator transforms the program.** The Core term is not shaped like the source, so a correctness proof must
   track every rewrite (continuations, loop control, state threading, class lowering), each a proof case of its own.
3. **The checker's ownership soundness is a prerequisite and is unproved** (a 1,160-line checker).
4. **Per-file checks run the frontend and the elaborator in the kernel**, which does not scale: certifying a 250-line
   port of drive's `trust.ts` peaked at about 13.6 GB without completing; a `decide` on a safety predicate also hit
   13.6 GB.

### 2.3 What drive's kernel needs

Drive's subset (from its `docs/VERIFIED_KERNEL.md`), which is known to be sufficient for its kernel:

- **Types:** `number` (used as integers below 2^53), `string`, `boolean`, `T[]`, optional (`T | null`,
  `T | undefined`, `x?: T`), interfaces of those, unions of string literals, unions of object types told apart by a
  literal first property (`kind`, `state`, `ok`, including `ok: true | false`).
- **Declarations:** functions with typed parameters and results; no recursion or top-level values.
- **Classes with owned maps:** all fields `private f = new Map<K, V>()` (string or number keys). `this` only appears as
  `this.f.get(k)`, `this.f.has(k)`, `this.f.size`, `[...this.f.values()]` (or `keys()`, `entries()`),
  `this.f.set(k, v);`, `this.f.delete(k);` (statements of `void` methods), and `this.m(…)` statements. Drive translates
  a method to a function of the object's state returning the new state.
- **Statements:** `const`, `let`, reassignment of locals; `if`/`else` (including unbraced single statements);
  `for (const x of xs)`, `for (const [i, x] of xs.entries())`, counted `for (let i = 0; i < n; i++)`; `switch` on a tag
  or literal union with each case ending in `return`/`continue`/`break`; `return`; `continue`; `break`;
  `if (x == null) return …;` narrowing.
- **Expressions:** literals, locals, fields, calls to kernel functions; `!`, unary `-`, `&&`, `||`, `===`, `!==` (on
  primitives), `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, string `+` and `<`; `c ? a : b`, `x == null ? a : b`; array
  literals with spreads; object literals and `{ ...r, f: v }`; arrow functions; `xs.length`, `entries`, `some`,
  `every`, `map`, `filter`, `includes`, `toSorted`.
- **Not in it:** in-place change of records or arrays, `while`, other `for (;;)` loops, `==` other than `== null`, `/`,
  `%`, optional chaining, `typeof`, exceptions, async, constructors, inheritance, generics other than `Map<K, V>`,
  nested maps (composite string keys are used instead).

Drive's prelude **assumes** (does not check) that numbers stay below 2^53, that strings are well-formed UTF-16, and that
`null` and `undefined` are never told apart from each other. v2 should turn the number assumption into a checked safety
precondition.

When v1's checker was run on drive's kernel files, all three were rejected immediately (unbraced `if` bodies). Porting
`trust.ts` until v1's checker accepted it required: braces; replacing `for (const [i, f] of xs.entries())`; replacing
optional parameters; string tags instead of `ok: true | false`; inlining borrowed reads instead of binding them; making
every array and field `readonly`; inlining the comparator and helpers into callbacks (v1 callbacks cannot call user
functions); replacing a record-returning `map` by a loop; splitting fall-through `switch` cases. v1 extraction then also
needed `=== undefined` instead of `== null`, `some` instead of `includes`, `type` instead of `interface`, no `!`, and it
stopped at `f.commit === 'bad'` (comparison on a string-literal union). `registers.ts` and `tree.ts` also use private
methods. **v2 should accept drive's subset as written, or with minimal rewrites.**

## 3. Design principles

Every decision is subordinate to keeping the general theorem easy to state and prove.

1. **A value semantics as the trusted model.** In a language with no visible mutation and no identity comparison on
   objects, JavaScript's reference semantics coincides with a value semantics. The trusted model is therefore a big-step,
   fuel-indexed evaluator over plain JavaScript values (no heap), executable in Lean so it can be differentially tested
   against Node or Bun. Mutation enters only under a uniqueness discipline that keeps value semantics exact (section 9,
   levels L5 and L6), and a separate, optional proof can later relate the value semantics to a heap semantics.
2. **The typed program is the source plus types.** The translator produces an intrinsically typed syntax tree whose
   **erasure is exactly the parsed syntax tree**: one typed constructor per source construct, no desugaring, no
   rewriting. The type checker that builds it is untrusted; the per-file check is the structural equation
   `erase typed = parsed`, which the kernel checks by `rfl` cheaply.
3. **A compositional denotation directly on typed syntax.** Statements, mutable locals, loops, `break`, `continue` and
   early `return` are denoted into a small outcome type, so the source's control flow needs no translation.
4. **One theorem by induction on typed syntax.** Each new construct adds one case to one proof. There are no per-program
   proofs, and no tactic-driven proof generation.
5. **Readable output, checked by `rfl`.** The emitted Lean definitions are printed in a readable form and checked equal
   to the denotation per file. The printer is untrusted.
6. **Nothing expensive in the kernel per file.** Per-file kernel work is structural equality of terms (`erase`, the
   printed definitions against the denotation), never running a lexer, parser, checker or elaborator inside the kernel.
7. **Add features one level at a time, and stop where the proof becomes unmanageable.** Each level ships with the theorem
   extended to cover it, its tests, and its negative fixtures.

## 4. Architecture

```
source.ts ──parse (trusted, tested)──▶ ast : Program          (untyped, JavaScript-shaped)
                                          │
                     typecheck (untrusted)│
                                          ▼
                                   typed : TProgram           (intrinsically typed, erase typed = ast)
                                          │
                  print (untrusted)       │ denote (in Lean, defined once)
                                          ▼
                         Gen.lean: readable defs  ──rfl──▶  TProgram.denote typed

Proved once:   ∀ typed, safe → eval (erase typed) converges to encode (denote typed)
Checked per file (kernel):  erase typed = ast,   printed defs = denote typed
Concluded per file:          every printed def is what the TypeScript computes (in the model)
```

### 4.1 Trusted base

| Trusted | Why it is believable |
| --- | --- |
| The value-semantics model of the subset (`eval`, the builtin definitions) | Small, executable, one rule per construct, documented against ECMAScript; differentially tested against Node/Bun on hand fixtures and on random well-typed programs |
| The parser (TypeScript source to `ast`) | Untrusted in principle, but nothing checks it in the kernel (that is what made v1 expensive). Tested: differential against the TypeScript compiler's own parse, round-trip printing, fuzzing. Kernel-checking a cheap printing equation (`print ast = normalized source`) is an M0 measurement (section 11) |
| Lean's kernel | The usual base; the axiom audit allows only `propext`, `Quot.sound`, `Classical.choice` |

**Untrusted:** the type checker, the translator, the printer of Lean code, every tactic. A bug in any of them makes a
per-file check fail; it cannot produce a wrong theorem.

## 5. The trusted model

### 5.1 Syntax

`Expr`, `Stmt`, `Function`, `Program`: untyped and JavaScript-shaped, without source spans (the parser keeps spans in a
separate structure for diagnostics and strips them). Names are strings. The syntax covers exactly the constructs of the
levels implemented so far.

### 5.2 Values

```lean
inductive JSValue where
  | undefined | null
  | bool (b : Bool)
  | number (x : Float.Model)          -- binary64, from Lean core: Init.Data.Float.Model.Float
  | bigint (n : Int)
  | string (s : JSString)             -- List UInt16 (UTF-16 code units)
  | array (xs : List JSValue)
  | record (fields : List (String × JSValue))
  | closure (params : List String) (body : Stmt) (env : Env)
```

Records with optional fields: JavaScript distinguishes an absent field from a field holding `undefined` only through
`in`, `Object.keys`, enumeration and JSON, all excluded. The model may normalise (for example, record construction drops
fields whose value is `undefined`, and a missing field reads as `undefined`) so that the encoding of Lean values is a
function. Document whatever choice is made next to the rule.

### 5.3 Evaluation

```lean
def evalExpr  (p : Program) : Nat → Env → Expr → Except Fault JSValue
def execStmts (p : Program) : Nat → Env → List Stmt → Except Fault Outcome
def call      (p : Program) : Nat → String → List JSValue → Except Fault JSValue

inductive Outcome where
  | normal (env : Env) | returned (v : JSValue) | broke (env : Env) | continued (env : Env)

inductive Fault where
  | timeout | typeError (m : String) | rangeError (m : String) | thrown (m : JSString)
```

- `Env` is an association list from names to values. Declarations add a binding; assignment replaces it.
- Fuel bounds recursion depth. Prove fuel monotonicity once (`timeout` at fuel `n` refines any result at `n + 1`) and
  define `Converges f v := ∃ n, ∀ m ≥ n, f m = v`. v1's `Ariadne/Fuel.lean` and `Convergence.lean` show the pattern.
- Callbacks passed to builtins are closures over a snapshot of the environment. This equals JavaScript's capture by
  reference because callbacks may not assign captured variables and are consumed before any statement that could
  reassign them (enforce this in the typed syntax).
- Builtins (`map`, `filter`, `some`, `every`, `find`, `includes`, `toSorted`, `slice`, `length`, string comparison,
  numeric operations) are defined in the model by Lean functions with documented JavaScript behaviour. Reuse v1's
  definitions where they exist (section 10).

### 5.4 Numbers

Two modes, decided per type:

- **Integer mode (the default for `number`, and for `type Int53 = number`):** `number` denotes `Int`. Programs may use
  integer literals, `+`, `-`, `*`, unary `-`, comparisons, `===`, and `length`/indices. The safety predicate requires
  every intermediate result to stay within ±(2^53 − 1), so binary64 arithmetic is exact and coincides with `Int`
  arithmetic. This replaces drive's unchecked assumption. Watch for negative zero: `-x` with `x = 0`, and `0 * -1`,
  produce `-0` in binary64, so the value relation for integer-mode numbers must be "the float is the integer, or the
  integer is 0 and the float is −0", not equality with `Float.Model.ofInt n`. v1's `Ariadne/Shallow/Prelude/Int53Exact.lean`
  (about 1,200 lines) proves exactly these correspondences and should be reused.
- **Float mode (later):** `number` denotes `Float.Model` (binary64) for code that needs `/`, fractions, `NaN`.
- **`bigint`** denotes `Int` exactly. Division and remainder fault on zero; keep them out until faults are supported.

### 5.5 Strings, null and undefined

- Strings are `JSString = List UInt16`. `<` is code-unit order (v1's `Prelude/String.lean` has the order lemmas).
- `T | undefined`, `x?: T` and `T | null` denote `Option τ`. Each optional type records which nullish value encodes
  `none` (`undefined` for `?:` and `| undefined`, `null` for `| null`). Mixed `T | null | undefined` is accepted only if
  values of that type are never returned or stored where the distinction is observable; otherwise refuse. `x == null`
  and `x != null` are the only uses of `==`.

## 6. Typed syntax, erasure and well-formedness

```lean
inductive Ty where
  | bool | int | number | string | unit                                   -- unit is undefined/void
  | option (nullish : Nullish) (τ : Ty) | array (τ : Ty)
  | record (fields : List (String × Ty))                                  -- L1
  | union (tag : String) (variants : List (String × List (String × Ty)))  -- L1
  | fn (args : List Ty) (result : Ty)                                     -- callbacks, L2
  | map (key : Key) (value : Ty)                                          -- L5

abbrev Ctx := List (String × Ty)          -- names kept so erasure is exact

inductive TExpr : Ctx → Ty → Type         -- one constructor per source expression form
inductive TStmts : Ctx → Ty → Type        -- statement lists, context threaded through declarations
def TExpr.erase : TExpr Γ τ → Expr
def TStmts.erase : TStmts Γ τ → List Stmt
```

- **One typed constructor per source form**, carrying whatever erasure needs (names, operator spelling). Coercions that
  have no source syntax are not allowed; if a coercion is needed, it must be a no-op under `encode`.
- **Variables:** `Var Γ τ` is a de Bruijn index into a context of named bindings. To make name lookup in the model agree
  with the index, either forbid shadowing (the context's names are distinct; prove the needed lookup lemma once), or
  build the "first occurrence of the name" requirement into `Var`. Forbidding shadowing is simpler and drive's code
  does not shadow.
- **Restrictions are by construction where possible:** no `===` on non-primitive types, callbacks that do not assign
  captured variables, owned maps used only in the allowed positions (L5, L6). What cannot be expressed in the types is a
  decidable predicate `WellFormed typed`, proved per file by `decide` (keep it cheap and structural).
- **The type checker** is ordinary untrusted code that builds `TProgram` from `Program`, reporting diagnostics with
  codes like v1's (`docs/DIAGNOSTICS.md`). It may reuse v1's checker logic but nothing depends on its correctness.

## 7. Denotation and printed output

```lean
abbrev Ty.denote : Ty → Type              -- Int, Bool, JSString, Option, List, products/structures, ...
def TExpr.denote : TExpr Γ τ → Γ.denote → τ.denote
def TStmts.denote : TStmts Γ τ → Γ.denote → Result Γ τ
-- Result: normal (new environment), returned value, break, continue
```

- Mutable locals: the environment `Γ.denote` is a tuple; assignment replaces a component. A declaration extends the
  context for the rest of the list.
- Loops denote to combinators over the outcome type: `for…of` folds over the list, counted `for` over the integer range,
  measured `while` (L7 or L3b) by bounded iteration with v1's `Measured.bounded`/`bounded_unfold`. `break`, `continue`
  and early `return` are outcomes, so no continuation encoding is needed. v1's `Prelude/Loop.lean` and `Measured.lean`
  show the shapes.
- Records and unions denote to products and sums in the core theorem. For readable output, the printer may emit
  `structure` and `inductive` declarations together with per-file isomorphisms checked by `rfl`; the general theorem
  stays about the generic denotation, and per-file corollaries are restated through the isomorphism. Start with
  products and sums; add readable types as a printer feature once the theorem is stable.
- **Printed Lean:** readable definitions (`let`, `if`, `match`, named loop combinators), checked by
  `theorem f_eq : f = typed.denote f := by rfl` (or `simp only [denote, …]; rfl`, as v1's `DenotationChecks` do). Do
  not rely on Lean's `do` notation for the checked form unless a general lemma relates its desugaring to the
  denotation; `do` output can be offered as an extra, proved-equal view.
- Partial operations: the denotation is total. Where JavaScript can fault, the denotation returns a default and a
  separate **safety predicate** `safe` (computed from the same syntax, with the same budget for loops) says no fault and
  no out-of-range integer occurs. The theorem assumes `safe`. Keep the safety computation structural and cheap; it is
  stated as a hypothesis, never decided in the kernel on large inputs.

## 8. The theorem

```lean
/-- Encoding of Lean values as JavaScript values (a relation where −0 or absent fields require it). -/
def Represents : (τ : Ty) → JSValue → τ.denote → Prop

theorem adequacy (typed : TProgram) (f : typed.Fn args result) (xs : Args.denote args)
    (wf : typed.WellFormed) (safe : typed.safe f xs) :
    ∃ v, Converges (fun fuel => call typed.erase fuel f.name (encodeArgs xs)) (.ok v) ∧
      Represents result v (typed.denote f xs)
```

Proof: mutual induction on typed expressions and statement lists, with the invariant

```lean
def EnvRel (Γ : Ctx) (env : Env) (ρ : Γ.denote) : Prop :=
  ∀ {τ} (x : Var Γ τ), ∃ v, env.lookup x.name = some v ∧ Represents τ v (x.get ρ)
```

and, for statements, a relation between `Outcome` and the denoted result (normal/break/continue carry related
environments, returned carries a related value). Each level adds the cases for its constructs. Loops are handled by an
inner induction on the list (`for…of`), the range (counted `for`) or the measure (measured `while`, recursion).

**Per-file corollary,** emitted with each translation:

```lean
theorem f_source (xs …) (safe : f.safe xs) :
    ∃ v, Converges (fun fuel => call ast fuel "f" (encodeArgs xs)) (.ok v) ∧ Represents result v (f xs) :=
  erased ▸ f_eq ▸ adequacy typed …
```

A user proves `P (f xs)` about the readable definition, and gets that every run of the TypeScript `f` (in the model)
returns a value representing a result satisfying `P`.

## 9. The feature ladder

Each level is a milestone: grammar and model rules, typed constructors, denotation, theorem cases, printer, tests,
negative fixtures, docs. Do not start a level before the previous one's theorem is complete, with no `sorry`.

| Level | Adds | Notes for the theorem |
| --- | --- | --- |
| **L0** | `boolean`, `bigint` (no `/`, `%`), `string` (literals, `+`, `===`, `<`); `const`; `if`/`else`; `return`; `&&`, `\|\|`, `!`, `?:`; calls to earlier functions (call graph acyclic, in declaration order) | Pure expressions and straight-line statements. Calls: denote functions in program order; the evaluator's call rule binds arguments in a fresh environment |
| **L1** | readonly records and object literals, `{ ...r, f: v }`, field reads; string-literal unions; unions of records tagged by a literal field (string, and `true`/`false`); `switch` with narrowing; optional fields and values, `== null`, `!= null`, `??`, `if (x == null) return …;` narrowing; `interface` and `type` declarations | Narrowing: a `switch` or `== null` test binds a refined variable in the typed syntax; erasure keeps the original source |
| **L2** | readonly arrays, array literals with spreads, `length`, indexing (`T \| undefined`), `includes` (primitives), `some`, `every`, `map`, `filter`, `find`, `toSorted` (comparator), `entries`; typed arrow-function callbacks that may call user functions and capture `const` (and not-yet-reassigned) bindings | Callbacks are closures in the model; the theorem case relates closure application to denoted functions. Sorting: reuse v1's `Prelude/Sort.lean` (stable merge sort equalities) |
| **L3** | `let` and reassignment of locals; `for (const x of xs)`, `for (const [i, x] of xs.entries())`, counted `for (let i = 0; i < n; i++)`; `break`, `continue`, early `return` inside loops; `switch` cases ending in `break`/`continue`/`return` | Environment updates and outcomes; inner inductions for loops. This level is the core of drive's code |
| **L4** | `number` in integer mode with the safety predicate (section 5.4); `type Int53 = number`; faults where needed | Port drive's `trust.ts` here and prove drive's `Spec/Trust.lean` statements about the output (acceptance test) |
| **L5** | **owned local collections:** `new Map<K, V>()`, `new Set<K>()` and `[]` held by exactly one `let`/`const` binding, mutated only by statements `m.set`, `m.delete`, `xs.push`, read by `get`, `has`, `size`, `keys()/values()/entries()` copies, returned or passed only as the last use | Under this uniqueness discipline, in-place mutation equals rebinding (`m := m.set k v`), so the model stays a value semantics. The discipline is enforced by the typed syntax (an owned binding sort). Map model: reuse v1's `Prelude/Map.lean` (`JSMap`, insertion order, SameValueZero keys via `NumberKey.lean`) |
| **L6** | **classes with owned maps** (drive's discipline, section 2.3): private `Map` fields, `void` methods that change the state, value methods that do not, `this.m(…)` statements; also mutable parameters as "backward functions" (a function mutating its parameter returns the new value, and the caller rebinds it), only with distinct argument roots | A method denotes a function of the object state returning the new state. Port drive's `registers.ts` and `tree.ts` here |
| **L7** | measured `while` (`/** @decreases m */`), measured recursion, `throw new Error("literal")` as a `Sum`/`Except` result | v1 implemented all three for its Core (`Measured.bounded`, `fixBounded`, `bounded_unfold`, `fixBounded_unfold`, throw lowering); reuse the library lemmas |
| **L8 (optional)** | a heap semantics for the subset with L5/L6 mutation, and a proof that it agrees with the value semantics under the uniqueness discipline | Removes "value semantics is exact for owned mutation" from the trusted base |

**Where it may get too hard:** L6 (classes, backward functions) and L8. If the theorem's proof grows faster than
linearly in the number of constructs, or a level needs global invariants beyond the environment relation, stop and
reassess before adding more.

## 10. What to reuse from v1

All paths below are on this branch (inherited from `claude/design-certified-shallow-translation`). Copy them into the
new tree rather than importing v1 modules, so that v1 can be deleted wholesale later. Check each one's imports: most
depend only on `Ariadne.Value`, which itself should be rewritten for v2 (section 5.2).

| v1 file | What it provides |
| --- | --- |
| Lean core `Init.Data.Float.Model.Float` | `Float.Model` (binary64), already used by v1 |
| `Ariadne/Value.lean` | `JSString`, v1's `Value`/`Object` (heap-based; replace with `JSValue`) |
| `Ariadne/Builtins.lean` | `numberTrunc`, `numberFloor`, `numberString` (number to string), string search, `join` |
| `Ariadne/Shallow/Prelude/Int53.lean`, `Int53Exact.lean` | safe-integer range and exactness of binary64 integer arithmetic, including −0 handling |
| `Ariadne/Shallow/Prelude/String.lean` | code-unit order, composite-key injectivity (`a + '\0' + b`) |
| `Ariadne/Shallow/Prelude/Array.lean` | JavaScript array builtins as list functions (`get`, `slice`, `map`, `filter`, `reduce`, `some`, `every`, `find`, `findIndex`) |
| `Ariadne/Shallow/Prelude/Sort.lean` | stable sort equalities for `toSorted` |
| `Ariadne/Shallow/Prelude/Map.lean`, `Set.lean`, `NumberKey.lean`, `NumericCollections.lean` | `JSMap`/`JSSet` with insertion order and SameValueZero numeric keys |
| `Ariadne/Shallow/Prelude/Loop.lean`, `Measured.lean` | loop combinators, `Step`/`Exit`, measured iteration and recursion with their unfolding lemmas |
| `Ariadne/Fuel.lean`, `Convergence.lean` | patterns for fuel monotonicity and `Converges` |
| `Ariadne/Lexer.lean`, `Parser.lean`, `Syntax.lean` | a working lexer and parser for a close subset (v1 requires braces; v2 should accept unbraced single statements) |
| `Ariadne/Check.lean` | checker logic and diagnostics to borrow from for the untrusted type checker |
| `scripts/differential.mjs` and `scripts/shallow-*.mjs` | the three-way comparison pattern (TypeScript in Node, the Lean evaluator by `#eval`, the generated definitions by `#eval`) and JSON observations of values |
| `scripts/negative.mjs`, `examples/negative/` | negative-fixture harness (`// expected: CODE`) |
| `scripts/Audit.lean` | the axiom audit |
| `.github/workflows/ci.yml`, `scripts/install-ci-tools.sh`, `scripts/check.sh` | pinned CI (actions pinned by SHA, checksum-pinned Lean, elan and Bun), no build cache, serial kernel checks |
| `examples/reference/*.ts`, `Examples/Proofs/Reference*.lean` | the three reference programs and their native specifications (convergence, idempotence, permutation invariance, root reachability) as further acceptance targets |

From drive (repository [nathsou/drive](https://github.com/nathsou/drive)): `core/kernel/*.ts` (the target programs),
`verify/Drive/Spec/*.lean` (the statements to prove), `verify/Drive/JS/Prelude.lean` (its JavaScript model, a useful
cross-check for v2's builtins), `scripts/verify/differential.ts` and `parse.ts` (its differential testing and
TypeScript-parse cross-check), and its soundness gate (spec lock, axiom audit, source lint; see its
`docs/VERIFIED_KERNEL.md`, "Soundness of the proofs").

**Do not reuse:** the heap evaluator as the trusted model, the shallow elaborator and its plans (`StatePlan`,
`ClassPlan`, projections, joins), the ownership checker, the heap WP library and adequacy proofs, and the kernel
certificates for lexing and parsing.

## 11. Milestones

Each milestone ends with CI green, the axiom audit clean, docs updated, and a short status entry in
`docs/V2-PROGRESS.md` (create it in M0).

- **M0: scaffolding and measurements.**
  - A new Lean library (for example `lean_lib V2` with root `V2.lean`) in this package, importing nothing from
    `Ariadne`. A new executable (for example `ariadne2`) with `check` and `extract` commands. Legacy targets stay as they
    are until v2 reaches L4; the legacy CI phases may be dropped from the default CI run to save time.
  - Copy the reused models (section 10) into `V2/Model/`.
  - Measure, on a file the size of drive's `trust.ts` (about 250 lines, 10 functions): the kernel time and peak memory of
    the per-file checks (`erase typed = ast`, printed definitions `= denote`), and of a kernel check of
    `print ast = normalized source` if the parser is to be checked. Target: under 2 GB and under a minute per file;
    decide the parser's status from the measurement.
- **M1: L0 end to end.** Model, typed syntax, erasure, denotation, printer, `adequacy` proved for L0, CLI, a
  random well-typed program generator, the three-way differential test, negative fixtures.
- **M2: L1. M3: L2. M4: L3.** Each with the theorem extended and tests.
- **M5: L4 and drive's trust kernel.** Translate drive's `trust.ts` (rewritten as little as necessary; record each
  rewrite), prove drive's `Spec/Trust.lean` statements about the output, and transfer them to the TypeScript. This is
  the first end-to-end demonstration.
- **M6: L5. M7: L6 and drive's registers and tree.** Prove drive's `Spec/Registers.lean` (`converges`, `once`,
  `lookups`).
- **M8: L7.** **M9 (optional): L8.**
- **Checkpoint after M4:** compare the size of the adequacy proof per construct. If it is growing faster than linearly,
  or a level needed global invariants, stop and write up the reason before continuing.
  Done (see `V2-PROGRESS.md`): growth is linear with a falling slope; continue. Plan changes recorded there: numbers
  moved into L2, so L4 is drive's `trust.ts`; counted `for` moves to L7.

When v2 covers L4 and the reference programs it can express, delete v1's code from the tree (the history and the
draft PR keep it).

## 12. Testing and soundness gates

- **Three-way differential tests** for every fixture and for random programs: TypeScript run in Node or Bun, the model
  `call` evaluated by `#eval`, and the generated definitions evaluated by `#eval`. Observations are tagged JSON
  (`["bigint", "12"]`, `["string", [code units]]`, `["number", bits]`) as in v1's scripts. Under integer mode, compare
  only when the safety predicate holds, and check that it fails on inputs that overflow.
- **Random well-typed programs:** a generator over the typed syntax for each level, printed as TypeScript; this is the
  main defence of the trusted model.
- **Parser checks:** differential against the TypeScript compiler's parse (drive's `scripts/verify/parse.ts` does this
  with Bun), round-trip printing, fuzzing.
- **Negative fixtures** for every refusal, with stable diagnostic codes.
- **Axiom audit:** no axioms beyond `propext`, `Quot.sound`, `Classical.choice`; `sorry` and `native_decide` show up as
  axioms. Consider drive's spec lock (statements of the general theorem and of acceptance theorems are locked; a change
  is a visible diff) and source lint.
- **CI:** pinned tools, no build cache (Lean imports compiled modules without re-checking their proofs), kernel-heavy
  modules checked serially.

## 13. Lessons from v1 (practical)

- **Kernel evaluation is expensive.** `kernel_rfl` of the whole frontend, and `decide` on a safety predicate over a
  real program, each reached about 13.6 GB. Keep per-file kernel work structural. Never `decide` anything whose
  evaluation runs a program on large inputs.
- **Anything the kernel must reduce must be structurally recursive.** Well-founded recursion (including mutual
  `let rec` inside a definition) blocks kernel reduction: an elaboration equation failed until a helper was rewritten as
  one fuel-structural function.
- **Guard analyses against exponential blow-up.** An analysis following calls without a visited set hung the
  extractor on a recursive function with two recursive branches.
- **Memory:** the container and CI runners have about 16 GB. Parallel `lake build` of several heavy modules got killed
  (exit 137); build heavy modules one at a time, and run kernel-heavy CI phases serially.
- **Tactics:** `simp +arith` can loop on integer comparisons; `<;>` inside a macro used as a simp discharger enables
  error recovery and hides failures; `first | a | b` reports only the last alternative's error; irreducible predicates
  need an explicit `unfold` inside lemmas; heartbeat limits are a symptom of a tactic doing too much, so fix the tactic
  rather than raise the limit.
- **Hygiene in generated proofs:** generated text must qualify names that are not opened in the generated namespace,
  and `s!` strings must escape `{` as `{`.
- **Differential tests catch model mistakes early;** keep them running at every level.

## 14. Environment notes

- Lean toolchain: `leanprover/lean4:v4.35.0` (`lean-toolchain`). CI downloads it and Bun 1.4.3 with pinned SHA-256
  hashes (`scripts/install-ci-tools.sh`), with no toolchain manager. `lake build <Module>` builds one module.
- JavaScript: Node 22 runs `.ts` files directly (type stripping), which v1's test scripts rely on; CI uses Bun.
- The drive repository may not be in a new session's container; reference it on GitHub or attach it.

## 15. Open decisions

1. **Parser trust:** test only, or also kernel-check a printing equation (decide from the M0 measurement)?
2. **Readable records and unions:** products and sums first, `structure`/`inductive` with per-file isomorphisms later,
   or the reverse?
3. **Optional `null`/`undefined`:** which mixed forms to accept (section 5.5).
4. **Float mode for `number`:** needed for drive? (Drive's kernel uses no `/`.) Defer unless a target needs it.
5. **Naming:** library and executable names for v2, and whether to keep the `ariadne` name for the new tool once v1 is
   removed.
6. **Disposition of v1's draft PR** ([nathsou/ariadne#4](https://github.com/nathsou/ariadne/pull/4)): leave it open as a
   record, close it, or merge parts (the models) before deleting the rest.

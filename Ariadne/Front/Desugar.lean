import Ariadne.Parse.Parser

/-!
# Source forms written as other source forms

Trusted, as the converter is (it runs first in `convertProgram`; the type checker runs it too, so that the typed
program it builds is of the same forms). Each rewrite keeps JavaScript's meaning:

- A reference to a top-level constant `c` is the call `c()` of a function returning its value. A constant's value
  is a literal, `-` of one, or `+`, `-`, `*` of earlier constants and literals, so evaluating it again gives the same
  value, and reading it never meets its temporal dead zone (functions run after the module's constants are set,
  and a constant reads only earlier ones).
- `Math.max(a, b)` and `Math.min(a, b)` are the model's `max` and `min` operators (on numbers only: the model faults
  on others, as JavaScript throws on bigints).
- `m.has(k)` on a local `Map` is `m.get(k) != null`, the same whenever no value is `undefined` (which `get` requires).

**Changes in place.** A local that a function changes in place is *owned*: nothing else refers to its object, so
changing the object equals giving the local a new value, which is what the model does. The statements

- `xs.push(a, …);` is `xs = [...xs, a, …];`, `xs.pop();` is `xs = xs.slice(0, -1);`, `xs.sort(c);` is
  `xs = xs.toSorted(c);`,
- `r.f = e;` is `r = { ...r, f: e };`,
- `m.set(k, v);` and `m.delete(k);` on a local `Map` are `m = mapPut(m, k, v);` and `m = mapDel(m, k);`
  (`Expr.mapPut`, `Expr.mapDel`: no source syntax),

with the local's `const` read as `let`, keep their meaning when the local is owned (`checkOwned`):

- it is declared in the function with a fresh object: an array, object or `new Map()` literal, a `filter`, `map`,
  `toSorted` or `slice` of an array, or a choice between fresh objects; a reassignment gives it a fresh one too;
- once its object may be referred to from elsewhere, it is not changed in place again. Its object escapes when the
  local is used as a value other than by reading it: as an argument or the value pushed or set, in an array or object
  literal (other than spread, which copies), assigned or bound to another name, as the result of `??` or `?:`. A
  local is read when it is a receiver (`xs.length`, `xs[i]`, `xs.some(…)`, `m.get(k)`, `r.f`), spread, or compared
  with `null`. A `return` ends the function, so what it returns may escape. An escape inside a loop counts for every
  change in the loop, since the next iteration comes after it; a local declared inside the loop is a new one each
  iteration;
- it is not changed in the body of a loop over it (`for (const x of xs)`), which iterates the live object.

**Optional chains.** `x?.p…` on a local `x` (`p…` the rest of the chain, up to parentheses, which the parser marks)
is `x == null ? undefined : x.p…`: JavaScript evaluates the rest only when `x` is not nullish.

**Maps of maps.** A class field holding maps of maps (`Map<string, Map<string, T>>`) changes an inner map in place
with `this.f.get(k)?.set(k2, v);` and `this.f.get(k)?.delete(k2);`, which are
`if (this.f.has(k)) this.f.set(k, mapPut(this.f.get(k) ?? new Map(), k2, v));` (and `mapDel`): the same when no
inner map is referred to from anywhere but its entry (`nestedOk`). So an inner map is stored only as a new one
(`this.f.set(k, new Map())`), and `this.f.get(k)` is read only as `(this.f.get(k) ?? new Map())`, the receiver of
`get` and `size`, or of `keys()` and `values()` spread at once; the field's `values()` are not read.
-/

namespace Ariadne.Front
open Ariadne.Parse (Diagnostic Checked Span Expr Stmt)

def refuse (span : Span) (what : String) : Checked α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset", span }

/-- Whether a constant's value is one the rewrite keeps the meaning of: literals, and `+`, `-`, `*` and unary `-`
of earlier constants and literals. -/
partial def constantValueOk (earlier : List String) : Expr → Bool
  | .literal _ _ => true
  | .var x _ => earlier.contains x
  | .unary "-" e _ => constantValueOk earlier e
  | .binary op a b _ => ["+", "-", "*"].contains op && constantValueOk earlier a && constantValueOk earlier b
  | _ => false

mutual
  partial def desugarExpr (consts : List String) : Expr → Checked Expr
    | .var x span => pure (if consts.contains x then .call (.var x span) [] span else .var x span)
    | .call (.member (.var "Math" _) m _) args span =>
      if m == "max" || m == "min" then
        match args with
        | [a, b] => return .binary m (← desugarExpr consts a) (← desugarExpr consts b) span
        | _ => refuse span s!"Math.{m} with other than two arguments"
      else return .call (.member (.var "Math" span) m span) (← args.mapM (desugarExpr consts)) span
    | .literal l span => pure (.literal l span)
    | .unary op a span => return .unary op (← desugarExpr consts a) span
    | .binary op a b span => return .binary op (← desugarExpr consts a) (← desugarExpr consts b) span
    | .conditional c a b span =>
      return .conditional (← desugarExpr consts c) (← desugarExpr consts a) (← desugarExpr consts b) span
    -- A call's callee is a name (a function, not a constant's value) or a member.
    | .call (.var f s) args span => return .call (.var f s) (← args.mapM (desugarExpr consts)) span
    | .call f args span => return .call (← desugarExpr consts f) (← args.mapM (desugarExpr consts)) span
    | .member e f span => return .member (← desugarExpr consts e) f span
    | .index e i span => return .index (← desugarExpr consts e) (← desugarExpr consts i) span
    | .array es span => return .array (← es.mapM (desugarExpr consts)) span
    | .record fs span => return .record (← fs.mapM fun (f, e) => return (f, ← desugarExpr consts e)) span
    | .lambda ps body span => return .lambda ps (← desugarStmt consts body) span
    | .newMap k v span => pure (.newMap k v span)
    | .newSet k span => pure (.newSet k span)
    | .newClass c args span => return .newClass c (← args.mapM (desugarExpr consts)) span
    | .spread e span => return .spread (← desugarExpr consts e) span

  partial def desugarStmt (consts : List String) : Stmt → Checked Stmt
    | .block ss span => return .block (← ss.mapM (desugarStmt consts)) span
    | .let_ m x t e span => return .let_ m x t (← desugarExpr consts e) span
    | .assign t e span => return .assign t (← desugarExpr consts e) span
    | .update t op e span => return .update t op (← desugarExpr consts e) span
    | .expr e span => return .expr (← desugarExpr consts e) span
    | .if_ c a b span => return .if_ (← desugarExpr consts c) (← desugarStmt consts a) (← desugarStmt consts b) span
    | .while_ c b span => return .while_ (← desugarExpr consts c) (← desugarStmt consts b) span
    | .for_ i c u b span =>
      return .for_ (← desugarStmt consts i) (← desugarExpr consts c) (← desugarStmt consts u) (← desugarStmt consts b) span
    | .forOf m x e b span => return .forOf m x (← desugarExpr consts e) (← desugarStmt consts b) span
    | .forOfPair m x y e b span => return .forOfPair m x y (← desugarExpr consts e) (← desugarStmt consts b) span
    | .measured e b span => return .measured (← desugarExpr consts e) (← desugarStmt consts b) span
    | .switch_ e cases span => return .switch_ (← desugarExpr consts e) (← cases.mapM fun (l, ss) => do
        return (← l.mapM (desugarExpr consts), ← ss.mapM (desugarStmt consts))) span
    | .return_ e span => return .return_ (← desugarExpr consts e) span
    | s => pure s
end

/-! ## Owned locals -/

/-- The local an in-place statement changes, with its rewrite as an assignment. -/
def inPlace : Stmt → Option (String × Expr)
  | .expr (.call (.member (.var x xs) "push" _) args span) _ =>
    if x == "this" then none else some (x, .array (.spread (.var x xs) xs :: args) span)
  | .expr (.call (.member (.var x xs) "pop" ms) [] span) _ =>
    if x == "this" then none
    else some (x, .call (.member (.var x xs) "slice" ms) [.literal (.number 0 0) span, .unary "-" (.literal (.number 1 0) span) span] span)
  | .expr (.call (.member (.var x xs) "sort" ms) [c] span) _ =>
    if x == "this" then none else some (x, .call (.member (.var x xs) "toSorted" ms) [c] span)
  | .expr (.call (.member (.var x xs) "set" _) [k, v] span) _ =>
    if x == "this" then none else some (x, .call (.var "#mapPut" span) [.var x xs, k, v] span)
  | .expr (.call (.member (.var x xs) "delete" _) [k] span) _ =>
    if x == "this" then none else some (x, .call (.var "#mapDel" span) [.var x xs, k] span)
  | .assign (.member (.var x xs) f _) e span =>
    if x == "this" then none else some (x, .record [("", .var x xs), (f, e)] span)
  | _ => none

/-- What an in-place statement evaluates before changing its local: the values it stores. -/
def inPlaceArgs : Stmt → List Expr
  | .expr (.call _ args _) _ => args
  | .assign _ e _ => [e]
  | _ => []

/-- Expressions whose value is a new object. -/
partial def freshValue : Expr → Bool
  | .array _ _ | .record _ _ | .newMap _ _ _ => true
  | .call (.member _ m _) _ _ => ["filter", "map", "toSorted", "slice"].contains m
  | .conditional _ a b _ => freshValue a && freshValue b
  | _ => false

/-- Methods that read their receiver without keeping it. -/
def readMethods : List String :=
  ["includes", "some", "every", "find", "filter", "map", "toSorted", "slice", "get", "has", "keys", "values",
   "startsWith", "endsWith", "indexOf", "entries"]

/-- The locals of `owned` whose objects an expression may let escape (`inspect`: the expression's value is only
read). -/
partial def escapes (owned : List String) (inspect : Bool) : Expr → List String
  | .var x _ => if !inspect && owned.contains x then [x] else []
  | .member e _ _ => escapes owned true e
  | .index e i _ => escapes owned true e ++ escapes owned false i
  | .call (.member e m _) args _ =>
    (if readMethods.contains m then escapes owned true e else escapes owned false e) ++ args.flatMap (escapes owned false)
  | .call f args _ => escapes owned false f ++ args.flatMap (escapes owned false)
  | .array es _ => es.flatMap fun
    | .spread e _ => escapes owned true e
    | e => escapes owned false e
  | .record fs _ => fs.flatMap fun (f, e) => escapes owned f.isEmpty e
  | .conditional c a b _ => escapes owned false c ++ escapes owned inspect a ++ escapes owned inspect b
  | .binary op a b _ =>
    if ["==", "!=", "===", "!=="].contains op then escapes owned true a ++ escapes owned true b
    else if op == "??" then escapes owned inspect a ++ escapes owned inspect b
    else escapes owned false a ++ escapes owned false b
  | .unary _ a _ => escapes owned false a
  | .lambda _ body _ => stmtExprs body |>.flatMap (escapes owned false)
  | .spread e _ => escapes owned true e
  | .newClass _ args _ => args.flatMap (escapes owned false)
  | _ => []
where
  stmtExprs : Stmt → List Expr
    | .return_ e _ => [e]
    | _ => []

/-- Names a statement declares, at any depth. -/
partial def declaredIn : Stmt → List String
  | .let_ _ x _ _ _ => [x]
  | .block ss _ => ss.flatMap declaredIn
  | .if_ _ a b _ => declaredIn a ++ declaredIn b
  | .while_ _ b _ | .measured _ b _ => declaredIn b
  | .for_ i _ u b _ => declaredIn i ++ declaredIn u ++ declaredIn b
  | .forOf _ x _ b _ => x :: declaredIn b
  | .forOfPair _ x y _ b _ => x :: y :: declaredIn b
  | .switch_ _ cases _ => cases.flatMap (·.2.flatMap declaredIn)
  | _ => []

/-- Names a statement declares with `const` or `let`, at any depth (not loop variables). -/
partial def letsIn : Stmt → List String
  | .let_ _ x _ _ _ => [x]
  | .block ss _ => ss.flatMap letsIn
  | .if_ _ a b _ => letsIn a ++ letsIn b
  | .while_ _ b _ | .measured _ b _ => letsIn b
  | .for_ i _ u b _ => letsIn i ++ letsIn u ++ letsIn b
  | .forOf _ _ _ b _ | .forOfPair _ _ _ _ b _ => letsIn b
  | .switch_ _ cases _ => cases.flatMap (·.2.flatMap letsIn)
  | _ => []

/-- The locals a statement changes in place, at any depth. -/
partial def changedIn : Stmt → List String
  | .block ss _ => ss.flatMap changedIn
  | .if_ _ a b _ => changedIn a ++ changedIn b
  | .while_ _ b _ | .measured _ b _ => changedIn b
  | .for_ i _ u b _ => changedIn i ++ changedIn u ++ changedIn b
  | .forOf _ _ _ b _ | .forOfPair _ _ _ _ b _ => changedIn b
  | .switch_ _ cases _ => cases.flatMap (·.2.flatMap changedIn)
  | s => match inPlace s with
    | some (x, _) => [x]
    | none => []

/-- The local a loop iterates, if it iterates one directly. -/
def iterated : Expr → Option String
  | .var x _ => some x
  | .call (.member (.var x _) "entries" _) [] _ => some x
  | _ => none

/-- Checks a statement list against the ownership rules, given the owned locals whose objects may have escaped
(`frozen`); returns those after it. -/
partial def checkOwned (owned : List String) (frozen : List String) : List Stmt → Checked (List String)
  | [] => pure frozen
  | st :: rest => do
    let esc (e : Expr) := escapes owned false e
    let frozen ← match st with
      | .return_ _ _ => pure frozen
      | .let_ _ x _ e span => do
        if owned.contains x && !freshValue e then
          refuse span s!"changing '{x}' in place unless it starts as a new array, object or Map"
        pure (frozen ++ esc e)
      | .assign (.var x _) e span => do
        if owned.contains x && !freshValue e then
          refuse span s!"assigning '{x}', which is changed in place, other than a new array, object or Map"
        pure ((frozen ++ esc e).filter (· != x))
      | .if_ c a b _ => do
        let f := frozen ++ esc c
        let fa ← checkOwned owned f [a]
        let fb ← checkOwned owned f [b]
        pure (fa ++ fb).eraseDups
      | .block ss _ => checkOwned owned frozen ss
      | .switch_ e cases _ => checkOwned owned (frozen ++ esc e) (cases.flatMap (·.2))
      | .while_ c body _ => loopOwned owned (frozen ++ esc c) body none
      | .measured _ body _ => loopOwned owned frozen body none
      | .for_ init c u body _ => do
        let f ← checkOwned owned frozen [init]
        loopOwned owned (f ++ esc c) (.block [body, u] body.span) none
      | .forOf _ _ e body _ | .forOfPair _ _ _ e body _ => loopOwned owned (frozen ++ esc e) body (iterated e)
      | st => match inPlace st with
        | some (x, _) => do
          let f := frozen ++ (inPlaceArgs st).flatMap esc
          if f.contains x then
            refuse st.span s!"changing '{x}' in place after its object may be referred to from elsewhere"
          pure f
        | none => match st with
          | .expr e _ | .update _ _ e _ => pure (frozen ++ esc e)
          | _ => pure frozen
    checkOwned owned frozen rest
where
  /-- A loop's body, run twice: an escape in one iteration comes before the changes of the next. -/
  loopOwned (owned frozen : List String) (body : Stmt) (over : Option String) : Checked (List String) := do
    if let some x := over then
      if (changedIn body).contains x then refuse body.span s!"changing '{x}' in place while iterating over it"
    let fresh := declaredIn body
    let f ← checkOwned owned frozen [body]
    checkOwned owned (f.filter (!fresh.contains ·)) [body]

mutual
  /-- In-place statements on owned locals as assignments; their declarations as `let`. -/
  partial def rewriteOwned (owned : List String) : Stmt → Stmt
    | .let_ false x t e span => if owned.contains x then .let_ true x t e span else .let_ false x t e span
    | .block ss span => .block (ss.map (rewriteOwned owned)) span
    | .if_ c a b span => .if_ c (rewriteOwned owned a) (rewriteOwned owned b) span
    | .while_ c b span => .while_ c (rewriteOwned owned b) span
    | .measured e b span => .measured e (rewriteOwned owned b) span
    | .for_ i c u b span => .for_ (rewriteOwned owned i) c (rewriteOwned owned u) (rewriteOwned owned b) span
    | .forOf m x e b span => .forOf m x e (rewriteOwned owned b) span
    | .forOfPair m x y e b span => .forOfPair m x y e (rewriteOwned owned b) span
    | .switch_ e cases span => .switch_ e (cases.map fun (l, ss) => (l, ss.map (rewriteOwned owned))) span
    | st => match inPlace st with
      | some (x, e) => .assign (.var x st.span) e st.span
      | none => st
end

/-- `m.has(k)` on a local map as `m.get(k) != null`. -/
partial def rewriteHas : Expr → Expr
  | .call (.member (.member (.var "this" s1) f s2) "has" s3) args span =>
    .call (.member (.member (.var "this" s1) f s2) "has" s3) (args.map rewriteHas) span
  | .call (.member m "has" s1) [k] span =>
    .binary "!=" (.call (.member (rewriteHas m) "get" s1) [rewriteHas k] span) (.literal .null span) span
  | .unary op a span => .unary op (rewriteHas a) span
  | .binary op a b span => .binary op (rewriteHas a) (rewriteHas b) span
  | .conditional c a b span => .conditional (rewriteHas c) (rewriteHas a) (rewriteHas b) span
  | .call f args span => .call (rewriteHas f) (args.map rewriteHas) span
  | .member e f span => .member (rewriteHas e) f span
  | .index e i span => .index (rewriteHas e) (rewriteHas i) span
  | .array es span => .array (es.map rewriteHas) span
  | .record fs span => .record (fs.map fun (f, e) => (f, rewriteHas e)) span
  | .lambda ps (.return_ e s1) span => .lambda ps (.return_ (rewriteHas e) s1) span
  | .spread e span => .spread (rewriteHas e) span
  | .newClass c args span => .newClass c (args.map rewriteHas) span
  | e => e

partial def rewriteHasStmt : Stmt → Stmt
  | .block ss span => .block (ss.map rewriteHasStmt) span
  | .let_ m x t e span => .let_ m x t (rewriteHas e) span
  | .assign t e span => .assign (rewriteHas t) (rewriteHas e) span
  | .update t op e span => .update t op (rewriteHas e) span
  | .expr e span => .expr (rewriteHas e) span
  | .if_ c a b span => .if_ (rewriteHas c) (rewriteHasStmt a) (rewriteHasStmt b) span
  | .while_ c b span => .while_ (rewriteHas c) (rewriteHasStmt b) span
  | .measured e b span => .measured e (rewriteHasStmt b) span
  | .for_ i c u b span => .for_ (rewriteHasStmt i) (rewriteHas c) (rewriteHasStmt u) (rewriteHasStmt b) span
  | .forOf m x e b span => .forOf m x (rewriteHas e) (rewriteHasStmt b) span
  | .forOfPair m x y e b span => .forOfPair m x y (rewriteHas e) (rewriteHasStmt b) span
  | .switch_ e cases span => .switch_ (rewriteHas e) (cases.map fun (l, ss) => (l.map rewriteHas, ss.map rewriteHasStmt)) span
  | .return_ e span => .return_ (rewriteHas e) span
  | s => s

/-! ## Optional chains and maps of maps -/

/-- `this.f.get(k)`. -/
def stateGetOf : Expr → Option (String × Expr)
  | .call (.member (.member (.var "this" _) f _) "get" _) [k] _ => some (f, k)
  | _ => none

/-- An optional chain: its receiver, and the chain as a function of it. -/
partial def chainOf : Expr → Option (Expr × (Expr → Expr))
  | .member (.unary "?." base _) f span => some (base, fun r => .member r f span)
  | .member e f span => (chainOf e).map fun (b, k) => (b, fun r => .member (k r) f span)
  | .call e args span => (chainOf e).map fun (b, k) => (b, fun r => .call (k r) args span)
  | .index e i span => (chainOf e).map fun (b, k) => (b, fun r => .index (k r) i span)
  | _ => none

mutual
  /-- Optional chains on locals as conditionals; parentheses marks dropped. -/
  partial def chainsExpr (e : Expr) : Checked Expr := do
    match chainOf e with
    | some (.var x xs, k) =>
      let span := e.span
      chainsExpr (.conditional (.binary "==" (.var x xs) (.literal .null span) span) (.literal .undefined span) (k (.var x xs))
        span)
    | some (b, _) => refuse b.span "optional chaining on a receiver other than a local"
    | none => match e with
      | .unary "#paren" a _ => chainsExpr a
      | .unary "?." a _ => refuse a.span "this optional chain"
      | .unary op a span => return .unary op (← chainsExpr a) span
      | .binary op a b span => return .binary op (← chainsExpr a) (← chainsExpr b) span
      | .conditional c a b span => return .conditional (← chainsExpr c) (← chainsExpr a) (← chainsExpr b) span
      | .call f args span => return .call (← chainsExpr f) (← args.mapM chainsExpr) span
      | .member a f span => return .member (← chainsExpr a) f span
      | .index a i span => return .index (← chainsExpr a) (← chainsExpr i) span
      | .array es span => return .array (← es.mapM chainsExpr) span
      | .record fs span => return .record (← fs.mapM fun (f, e) => return (f, ← chainsExpr e)) span
      | .lambda ps body span => return .lambda ps (← chainsStmt [] body) span
      | .spread a span => return .spread (← chainsExpr a) span
      | .newClass c args span => return .newClass c (← args.mapM chainsExpr) span
      | e => pure e

  /-- `this.f.get(k)?.set(k2, v);` and `?.delete(k2);` on a map of maps (`nested`), then optional chains. -/
  partial def chainsStmt (nested : List String) : Stmt → Checked Stmt
    | .expr (.call (.member (.unary "?." g _) m _) args span) sspan => do
      match stateGetOf g, m, args with
      | some (f, k), "set", [k2, v] =>
        if !nested.contains f then refuse span s!"'?.set' on '{f}', which does not hold maps of maps"
        let inner := Expr.binary "??" g (.newMap .string .undefined span) span
        let put := Expr.call (.var "#mapPut" span) [inner, k2, v] span
        chainsStmt nested (.if_ (.call (.member (.member (.var "this" span) f span) "has" span) [k] span)
          (.expr (.call (.member (.member (.var "this" span) f span) "set" span) [k, put] span) sspan) (.block [] span) sspan)
      | some (f, k), "delete", [k2] =>
        if !nested.contains f then refuse span s!"'?.delete' on '{f}', which does not hold maps of maps"
        let inner := Expr.binary "??" g (.newMap .string .undefined span) span
        let del := Expr.call (.var "#mapDel" span) [inner, k2] span
        chainsStmt nested (.if_ (.call (.member (.member (.var "this" span) f span) "has" span) [k] span)
          (.expr (.call (.member (.member (.var "this" span) f span) "set" span) [k, del] span) sspan) (.block [] span) sspan)
      | _, _, _ => return .expr (← chainsExpr (.call (.member (.unary "?." g span) m span) args span)) sspan
    | .block ss span => return .block (← ss.mapM (chainsStmt nested)) span
    | .let_ m x t e span => return .let_ m x t (← chainsExpr e) span
    | .assign t e span => return .assign (← chainsExpr t) (← chainsExpr e) span
    | .update t op e span => return .update t op (← chainsExpr e) span
    | .expr e span => return .expr (← chainsExpr e) span
    | .if_ c a b span => return .if_ (← chainsExpr c) (← chainsStmt nested a) (← chainsStmt nested b) span
    | .while_ c b span => return .while_ (← chainsExpr c) (← chainsStmt nested b) span
    | .measured e b span => return .measured e (← chainsStmt nested b) span
    | .for_ i c u b span =>
      return .for_ (← chainsStmt nested i) (← chainsExpr c) (← chainsStmt nested u) (← chainsStmt nested b) span
    | .forOf m x e b span => return .forOf m x (← chainsExpr e) (← chainsStmt nested b) span
    | .forOfPair m x y e b span => return .forOfPair m x y (← chainsExpr e) (← chainsStmt nested b) span
    | .switch_ e cases span => return .switch_ (← chainsExpr e) (← cases.mapM fun (l, ss) => do
        return (← l.mapM chainsExpr, ← ss.mapM (chainsStmt nested))) span
    | .return_ e span => return .return_ (← chainsExpr e) span
    | s => pure s
end

/-- `(this.f.get(k) ?? new Map())` for a map of maps `f`. -/
def innerOf (nested : List String) : Expr → Option Expr
  | .binary "??" g (.newMap _ _ _) _ => match stateGetOf g with
    | some (f, k) => if nested.contains f then some k else none
    | none => none
  | _ => none

/-- Whether an expression reads the maps of maps `nested` only as the rules allow (see the module docs). -/
partial def nestedOk (nested : List String) : Expr → Bool
  | .call (.member r m _) args _ =>
    match innerOf nested r with
    | some k => ["get", "keys", "values"].contains m && nestedOk nested k && args.all (nestedOk nested)
    | none => match r with
      | .member (.var "this" _) f _ =>
        (!nested.contains f || (m != "get" && m != "values" && m != "set")) && args.all (nestedOk nested)
      | r => nestedOk nested r && args.all (nestedOk nested)
  -- What the rewrite of `?.set` and `?.delete` stores (no source syntax).
  | .call (.var "#mapPut" _) (r :: args) _ | .call (.var "#mapDel" _) (r :: args) _ =>
    (innerOf nested r).isSome && args.all (nestedOk nested)
  | .call f args _ => nestedOk nested f && args.all (nestedOk nested)
  | .member r f _ => match innerOf nested r with
    | some k => f == "size" && nestedOk nested k
    | none => nestedOk nested r
  | .unary _ a _ | .spread a _ => nestedOk nested a
  | .binary _ a b _ | .index a b _ => nestedOk nested a && nestedOk nested b
  | .conditional c a b _ => nestedOk nested c && nestedOk nested a && nestedOk nested b
  | .array es _ | .newClass _ es _ => es.all (nestedOk nested)
  | .record fs _ => fs.all (nestedOk nested ·.2)
  | .lambda _ (.return_ e _) _ => nestedOk nested e
  | _ => true

partial def nestedStmtOk (nested : List String) : Stmt → Bool
  -- An inner map is stored new, or as the rewrite of `?.set` and `?.delete` makes it.
  | .expr (.call (.member (.member (.var "this" _) f _) "set" _) [k, v] _) _ =>
    nestedOk nested k && (!nested.contains f || (match v with
      | .newMap _ _ _ => true
      | .call (.var "#mapPut" _) _ _ | .call (.var "#mapDel" _) _ _ => true
      | _ => false)) && nestedOk nested v
  | .block ss _ => ss.all (nestedStmtOk nested)
  | .let_ _ _ _ e _ | .assign _ e _ | .update _ _ e _ | .expr e _ | .return_ e _ => nestedOk nested e
  | .if_ c a b _ => nestedOk nested c && nestedStmtOk nested a && nestedStmtOk nested b
  | .while_ c b _ => nestedOk nested c && nestedStmtOk nested b
  | .measured _ b _ => nestedStmtOk nested b
  | .for_ i c u b _ => nestedStmtOk nested i && nestedOk nested c && nestedStmtOk nested u && nestedStmtOk nested b
  | .forOf _ _ e b _ | .forOfPair _ _ _ e b _ => nestedOk nested e && nestedStmtOk nested b
  | .switch_ e cases _ => nestedOk nested e && cases.all fun (l, ss) => (l.all (nestedOk nested)) && ss.all (nestedStmtOk nested)
  | _ => true

def desugarFunction (consts : List String) (f : Parse.Function) (nested : List String := []) :
    Checked Parse.Function := do
  let body ← desugarStmt consts f.body
  let body := rewriteHasStmt (← chainsStmt nested body)
  if !nestedStmtOk nested body then
    refuse f.span "reading a map of maps other than as (this.f.get(k) ?? new Map()).get(…), size, keys() or values()"
  let owned := (changedIn body).eraseDups
  for x in owned do
    if f.params.any (·.name == x) then refuse f.span s!"changing the parameter '{x}' in place (the caller's object)"
    if !(letsIn body).contains x then refuse f.span s!"changing '{x}' in place: only locals declared with a new object"
  let _ ← checkOwned owned [] [body]
  return { f with body := rewriteOwned owned body }

def desugarProgram (p : Parse.Program) : Checked Parse.Program := do
  -- Constants, in order: each value reads only earlier ones.
  let mut consts : List String := []
  for f in p.functions do
    if f.constant then
      let .block [.return_ value _] _ := f.body | refuse f.span "this constant"
      if !constantValueOk consts value then
        refuse f.span "a constant whose value is not a literal or arithmetic on earlier constants"
      consts := consts ++ [f.name]
  let names := consts
  let functions ← p.functions.mapM (desugarFunction names)
  let classes ← p.classes.mapM fun c => do
    let nested := c.fields.filterMap fun fld => match fld.value with
      | .newMap _ (.map _ _) _ => some fld.name
      | _ => none
    return { c with methods := ← c.methods.mapM (desugarFunction names · nested) }
  return { p with functions, classes }

end Ariadne.Front

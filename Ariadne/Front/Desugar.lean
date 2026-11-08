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

- `xs.push(a, …);` is `xs = [...xs, a, …];`, `xs.sort(c);` is `xs = xs.toSorted(c);`,
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

def desugarFunction (consts : List String) (f : Parse.Function) : Checked Parse.Function := do
  let body ← desugarStmt consts f.body
  let owned := (changedIn body).eraseDups
  for x in owned do
    if f.params.any (·.name == x) then refuse f.span s!"changing the parameter '{x}' in place (the caller's object)"
    if !(letsIn body).contains x then refuse f.span s!"changing '{x}' in place: only locals declared with a new object"
  let _ ← checkOwned owned [] [body]
  return { f with body := rewriteHasStmt (rewriteOwned owned body) }

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
    return { c with methods := ← c.methods.mapM (desugarFunction names) }
  return { p with functions, classes }

end Ariadne.Front

import Ariadne.Parse.Parser
import Ariadne.Model.Syntax

/-!
# From parsed TypeScript to the model's syntax

Trusted: the theorems are about the converted program, so this must map each
accepted source form to the model construct with the same JavaScript meaning.
It drops spans and type annotations and refuses everything else; it makes no
typing decisions. The non-identity mappings, each with JavaScript's meaning:

- `x += e`, `x -= e` and `x *= e` on a local `x` are `x = x op e` (the parser produces this form; `x` is
  read before `e` is evaluated); `x++` and `x--` are `x = inc x` and `x = dec x`, which add one in `x`'s
  own numeric type (`1` or `1n`).
- An expression-bodied arrow `(ps) => e` is the model's `arrow ps e`.
- A single unbraced statement as an `if` branch or a `for…of` body is a
  one-statement list (it is not a block, but a single non-declaration statement has
  no scope effect).
- `for (const [i, x] of e.entries())` is `forEntries i x e`.
- `while (c) body` is `while_ c body` (an unbraced body is a one-statement list, as for `if`).
- `Math.floor(a / b)` is `binary floorDiv a b`. `Math` is the global object: no declaration may
  take the name.
- `s.startsWith(t)`, `s.slice(a, b)` and the like are `method` calls, which the model runs only on
  the receivers and arguments it has a meaning for.
- `for (let i = 0; i < n; i++) body` on a local `n` is `forRange i n body` (whose
  static check requires `n` constant and `i` not assigned in `body`).
- A class: `new C()` is the function `new C` returning a record of its fields, each
  a `new Map()` (field initializers run in order); a method `m(ps)` is the function
  `m` with parameters `this :: ps`, and a `void` method gets a final `return;`
  (which is what falling off its end does). `this.f.get(k)`, `this.f.has(k)`,
  `this.f.size`, `...this.f.keys()`, `...this.f.values()`, `this.f.set(k, v);`,
  `this.f.delete(k);` and `this.m(args)` are the model's `state*` and `callThis`
  forms. Methods are listed so that each comes after the methods it calls (the
  model finds functions by name, so their order has no meaning).
-/

namespace Ariadne.Front
open Ariadne.Parse (Diagnostic Checked Span)

def unsupported (span : Span) (what : String) : Checked α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset", span }

def convertUnary (span : Span) : String → Checked UnOp
  | "!" => pure .not
  | "-" => pure .neg
  | "++" => pure .inc
  | "--" => pure .dec
  | op => unsupported span s!"unary '{op}'"

def convertBinary (span : Span) : String → Checked BinOp
  | "+" => pure .add | "-" => pure .sub | "*" => pure .mul | "/" => pure .div | "%" => pure .mod
  | "===" => pure .eq | "!==" => pure .ne
  | "<" => pure .lt | "<=" => pure .le | ">" => pure .gt | ">=" => pure .ge
  | "&&" => pure .and | "||" => pure .or | "??" => pure .coalesce
  | "==" => pure .looseEq | "!=" => pure .looseNe
  | op => unsupported span s!"operator '{op}'"

/-- A decimal literal `mantissa × 10^exponent`, if it is a safe integer. -/
def integerLiteral (span : Span) (mantissa : Nat) (exponent : Int) : Checked Int := do
  let value : Option Nat :=
    if 0 ≤ exponent then some (mantissa * 10 ^ exponent.toNat)
    else if mantissa % 10 ^ (-exponent).toNat == 0 then some (mantissa / 10 ^ (-exponent).toNat) else none
  match value with
  | some n => if n ≤ 2 ^ 53 - 1 then pure n else unsupported span "a number literal outside the safe integer range"
  | none => unsupported span "a non-integer number literal"

def convertLiteral (span : Span) : Parse.Literal → Checked Lit
  | .boolean b => pure (.bool b)
  | .bigint n => pure (.bigint n)
  | .string units => pure (.string units)
  | .number m e => return .number (← integerLiteral span m e)
  | .undefined => pure .undefined
  | .null => pure .null

/-- The variable a counted loop's update increments: `i++`, `i += 1` or `i = i + 1`. -/
def incrementOf : Parse.Stmt → Option String
  | .assign (.var i _) (.unary "++" (.var i' _) _) _ => if i == i' then some i else none
  | .assign (.var i _) (.binary "+" (.var i' _) (.literal (.number 1 0) _) _) _ => if i == i' then some i else none
  | _ => none

/-- A declaration's name: not `Math`, which `Math.floor` refers to. -/
def declName (span : Span) (x : String) : Checked String :=
  if x == "Math" then unsupported span "a declaration named Math" else pure x

mutual
  def convertExpr : Parse.Expr → Checked Expr
    | .literal l span => return .lit (← convertLiteral span l)
    | .var x _ => pure (.var x)
    | .unary op e span => return .unary (← convertUnary span op) (← convertExpr e)
    | .binary op a b span => return .binary (← convertBinary span op) (← convertExpr a) (← convertExpr b)
    | .conditional c a b _ => return .cond (← convertExpr c) (← convertExpr a) (← convertExpr b)
    | .call (.var f span) args _ =>
      if f.startsWith "#" then unsupported span "a template literal" else return .call f (← convertExprs args)
    | .call (.member (.member (.var "this" _) f _) "get" _) [k] _ => return .stateGet f (← convertExpr k)
    | .call (.member (.member (.var "this" _) f _) "has" _) [k] _ => return .stateHas f (← convertExpr k)
    | .member (.member (.var "this" _) f _) "size" _ => pure (.stateSize f)
    | .call (.member (.var "this" _) m _) args _ => return .callThis m (← convertExprs args)
    | .newMap .string _ _ => pure .newMap
    | .call (.member (.var "Math" _) "floor" _) [.binary "/" a b _] _ =>
      return .binary .floorDiv (← convertExpr a) (← convertExpr b)
    | .call (.member e m _) args _ => return .method (← convertExpr e) m (← convertExprs args)
    | .member e f _ => return .field (← convertExpr e) f
    | .index e i _ => return .index (← convertExpr e) (← convertExpr i)
    | .array elems _ => return .array (← convertElems elems)
    | .record fields _ => return .record (← convertEntries fields)
    | .lambda params (.return_ e span) _ => do
      return .arrow (← params.mapM (declName span ·.name)) (← convertExpr e)
    | e => unsupported e.span "this expression"

  def convertExprs : List Parse.Expr → Checked (List Expr)
    | [] => pure []
    | e :: es => return (← convertExpr e) :: (← convertExprs es)

  def convertElems : List Parse.Expr → Checked (List (Bool × Expr))
    | [] => pure []
    | .spread (.call (.member (.member (.var "this" _) f _) "keys" _) [] _) _ :: es =>
      return (true, .stateKeys f) :: (← convertElems es)
    | .spread (.call (.member (.member (.var "this" _) f _) "values" _) [] _) _ :: es =>
      return (true, .stateValues f) :: (← convertElems es)
    | .spread e _ :: es => return (true, ← convertExpr e) :: (← convertElems es)
    | e :: es => return (false, ← convertExpr e) :: (← convertElems es)

  /-- Object literal entries; the parser marks `...e` with an empty name. -/
  def convertEntries : List (String × Parse.Expr) → Checked (List (Option String × Expr))
    | [] => pure []
    | (f, e) :: es => return (if f.isEmpty then none else some f, ← convertExpr e) :: (← convertEntries es)
end

mutual
  def convertStmt : Parse.Stmt → Checked Stmt
    | .let_ false x _ e span => return .const (← declName span x) (← convertExpr e)
    | .let_ true x _ e span => return .let_ (← declName span x) (← convertExpr e)
    | .assign (.var x _) e _ => return .assign x (← convertExpr e)
    | .return_ e _ => return .ret (← convertExpr e)
    | .if_ c yes no _ => return .ite (← convertExpr c) (← convertBranch yes) (← convertBranch no)
    | .block ss _ => return .block (← convertStmts ss)
    | .switch_ e cases _ => return .switch (← convertExpr e) (← convertCases cases)
    | .break_ _ => pure .brk
    | .continue_ _ => pure .cont
    | .forOf false x e body span => return .forOf (← declName span x) (← convertExpr e) (← convertBranch body)
    | .for_ (.let_ true i _ (.literal (.number 0 0) _) _) (.binary "<" (.var i₁ _) (.var n _) _) update body span =>
      if i₁ == i && incrementOf update == some i then return .forRange (← declName span i) n (← convertBranch body)
      else unsupported span "this for loop"
    | .while_ c body _ => return .while_ (← convertExpr c) (← convertBranch body)
    | .forOfPair false i x (.call (.member e "entries" _) [] _) (.block body _) span =>
      return .forEntries (← declName span i) (← declName span x) (← convertExpr e) (← convertStmts body)
    | .expr (.call (.member (.member (.var "this" _) f _) "set" _) [k, v] _) _ =>
      return .stateSet f (← convertExpr k) (← convertExpr v)
    | .expr (.call (.member (.member (.var "this" _) f _) "delete" _) [k] _) _ =>
      return .stateDelete f (← convertExpr k)
    | .expr (.call (.member (.var "this" _) m _) args _) _ => return .callThis m (← convertExprs args)
    | s => unsupported s.span "this statement"

  /-- An `if` branch: a braced block's statements, or one statement. -/
  def convertBranch : Parse.Stmt → Checked (List Stmt)
    | .block ss _ => convertStmts ss
    | .let_ _ _ _ _ span => unsupported span "a declaration as an unbraced branch"
    | s => return [← convertStmt s]

  def convertStmts : List Parse.Stmt → Checked (List Stmt)
    | [] => pure []
    | s :: ss => return (← convertStmt s) :: (← convertStmts ss)

  def convertCases : List (Option Parse.Expr × List Parse.Stmt) → Checked (List (Option Expr × List Stmt))
    | [] => pure []
    | (label, body) :: rest => do
      let label ← match label with
        | some t => some <$> convertExpr t
        | none => pure none
      return (label, ← convertStmts body) :: (← convertCases rest)
end

def convertFunction (f : Parse.Function) : Checked Function := do
  if f.decreases.isSome then unsupported f.span "a termination measure"
  let .block body _ := f.body | unsupported f.span "this function body"
  return { name := ← declName f.span f.name, params := ← f.params.mapM (declName f.span ·.name),
           body := ← convertStmts body }

mutual
  /-- The methods an expression calls on `this`. -/
  partial def thisCallsExpr : Parse.Expr → List String
    | .call (.member (.var "this" _) m _) args _ => m :: args.flatMap thisCallsExpr
    | .call f args _ => thisCallsExpr f ++ args.flatMap thisCallsExpr
    | .unary _ a _ | .member a _ _ | .spread a _ => thisCallsExpr a
    | .binary _ a b _ | .index a b _ => thisCallsExpr a ++ thisCallsExpr b
    | .conditional c a b _ => thisCallsExpr c ++ thisCallsExpr a ++ thisCallsExpr b
    | .array es _ | .newClass _ es _ => es.flatMap thisCallsExpr
    | .record fs _ => fs.flatMap (thisCallsExpr ·.2)
    | .lambda _ body _ => thisCallsStmt body
    | _ => []

  partial def thisCallsStmt : Parse.Stmt → List String
    | .block ss _ => ss.flatMap thisCallsStmt
    | .let_ _ _ _ e _ | .expr e _ | .return_ e _ => thisCallsExpr e
    | .assign a e _ | .update a _ e _ => thisCallsExpr a ++ thisCallsExpr e
    | .if_ c a b _ => thisCallsExpr c ++ thisCallsStmt a ++ thisCallsStmt b
    | .while_ c b _ | .measured c b _ => thisCallsExpr c ++ thisCallsStmt b
    | .for_ i c u b _ => thisCallsStmt i ++ thisCallsExpr c ++ thisCallsStmt u ++ thisCallsStmt b
    | .forOf _ _ e b _ | .forOfPair _ _ _ e b _ => thisCallsExpr e ++ thisCallsStmt b
    | .switch_ e cases _ => thisCallsExpr e ++ cases.flatMap fun (l, ss) =>
        (l.map thisCallsExpr).getD [] ++ ss.flatMap thisCallsStmt
    | _ => []
end

/-- Methods in source order, except that each comes after the methods it calls. -/
def orderMethods (ms : List Parse.Function) : Checked (List Parse.Function) := do
  let names := ms.map (·.name)
  let calls := ms.map fun m => ((thisCallsStmt m.body).filter (names.contains ·)).eraseDups
  let mut placed : List Parse.Function := []
  let mut left := ms.zip calls
  for _ in ms do
    match left.find? (fun (_, cs) => cs.all fun c => placed.any (·.name == c)) with
    | some (m, _) =>
      placed := placed ++ [m]
      left := left.filter (·.1.name != m.name)
    | none => break
  if let some (m, _) := left.head? then unsupported m.span "a method that calls itself (directly or not)"
  return placed

/-- A class: its constructor function, then its methods. -/
def convertClass (c : Parse.Class) : Checked (List Function) := do
  let _ ← declName c.span c.name
  if let some ctor := c.constructor_ then unsupported ctor.span "a constructor"
  let fields ← c.fields.mapM fun f => match f.value with
    | .newMap .string _ _ => pure f.name
    | _ => unsupported f.span "a field other than a Map with string keys"
  let init : Function :=
    { name := s!"new {c.name}", params := [], body := [.ret (.record (fields.map fun f => (some f, .newMap)))] }
  let methods ← (← orderMethods c.methods).mapM fun m => do
    let fn ← convertFunction m
    let body := if m.result matches .void then fn.body ++ [.ret (.lit .undefined)] else fn.body
    return { fn with params := "this" :: fn.params, body, method := true }
  return init :: methods

/-- The model program for a parsed file: its functions in source order, then its
class. Type declarations are erased. -/
def convertProgram (p : Parse.Program) : Checked Program := do
  if let some c := p.classes[1]? then unsupported c.span "a second class"
  let fns ← p.functions.mapM convertFunction
  match p.classes.head? with
  | some c => return fns ++ (← convertClass c)
  | none => return fns

end Ariadne.Front

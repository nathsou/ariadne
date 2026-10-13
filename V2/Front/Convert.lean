import V2.Parse.Parser
import V2.Model.Syntax

/-!
# From parsed TypeScript to the model's syntax

Trusted: the theorems are about the converted program, so this must map each
accepted source form to the model construct with the same JavaScript meaning.
It drops spans and type annotations and refuses everything else; it makes no
typing decisions. The non-identity mappings, each with JavaScript's meaning:

- `x += e`, `x -= e`, `x *= e` and `x++`, `x--` on a local `x` are `x = x op e`
  (the parser produces this form; `x` is read before `e` is evaluated).
- An expression-bodied arrow `(ps) => e` is the model's `arrow ps e`.
- A single unbraced statement as an `if` branch is a one-statement list (it is
  not a block, but a single non-declaration statement has no scope effect).
- `for (const [i, x] of e.entries())` is `forEntries i x e`.
-/

namespace V2.Front
open V2.Parse (Diagnostic Checked Span)

def unsupported (span : Span) (what : String) : Checked α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset", span }

def convertUnary (span : Span) : String → Checked UnOp
  | "!" => pure .not
  | "-" => pure .neg
  | op => unsupported span s!"unary '{op}'"

def convertBinary (span : Span) : String → Checked BinOp
  | "+" => pure .add | "-" => pure .sub | "*" => pure .mul
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

mutual
  def convertExpr : Parse.Expr → Checked Expr
    | .literal l span => return .lit (← convertLiteral span l)
    | .var x _ => pure (.var x)
    | .unary op e span => return .unary (← convertUnary span op) (← convertExpr e)
    | .binary op a b span => return .binary (← convertBinary span op) (← convertExpr a) (← convertExpr b)
    | .conditional c a b _ => return .cond (← convertExpr c) (← convertExpr a) (← convertExpr b)
    | .call (.var f span) args _ =>
      if f.startsWith "#" then unsupported span "a template literal" else return .call f (← convertExprs args)
    | .call (.member e m _) args _ => return .method (← convertExpr e) m (← convertExprs args)
    | .member e f _ => return .field (← convertExpr e) f
    | .index e i _ => return .index (← convertExpr e) (← convertExpr i)
    | .array elems _ => return .array (← convertElems elems)
    | .record fields _ => return .record (← convertEntries fields)
    | .lambda params (.return_ e _) _ => return .arrow (params.map (·.name)) (← convertExpr e)
    | e => unsupported e.span "this expression"

  def convertExprs : List Parse.Expr → Checked (List Expr)
    | [] => pure []
    | e :: es => return (← convertExpr e) :: (← convertExprs es)

  def convertElems : List Parse.Expr → Checked (List (Bool × Expr))
    | [] => pure []
    | .spread e _ :: es => return (true, ← convertExpr e) :: (← convertElems es)
    | e :: es => return (false, ← convertExpr e) :: (← convertElems es)

  /-- Object literal entries; the parser marks `...e` with an empty name. -/
  def convertEntries : List (String × Parse.Expr) → Checked (List (Option String × Expr))
    | [] => pure []
    | (f, e) :: es => return (if f.isEmpty then none else some f, ← convertExpr e) :: (← convertEntries es)
end

mutual
  def convertStmt : Parse.Stmt → Checked Stmt
    | .let_ false x _ e _ => return .const x (← convertExpr e)
    | .let_ true x _ e _ => return .let_ x (← convertExpr e)
    | .assign (.var x _) e _ => return .assign x (← convertExpr e)
    | .return_ e _ => return .ret (← convertExpr e)
    | .if_ c yes no _ => return .ite (← convertExpr c) (← convertBranch yes) (← convertBranch no)
    | .block ss _ => return .block (← convertStmts ss)
    | .switch_ e cases _ => return .switch (← convertExpr e) (← convertCases cases)
    | .break_ _ => pure .brk
    | .continue_ _ => pure .cont
    | .forOf false x e (.block body _) _ => return .forOf x (← convertExpr e) (← convertStmts body)
    | .forOfPair false i x (.call (.member e "entries" _) [] _) (.block body _) _ =>
      return .forEntries i x (← convertExpr e) (← convertStmts body)
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
  return { name := f.name, params := f.params.map (·.name), body := ← convertStmts body }

/-- The model program for a parsed file, in source order. Type declarations are
erased. -/
def convertProgram (p : Parse.Program) : Checked Program := do
  if let some c := p.classes.head? then unsupported c.span "a class"
  p.functions.mapM convertFunction

end V2.Front

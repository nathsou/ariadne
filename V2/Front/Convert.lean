import Ariadne.Parser
import V2.Model.Syntax

/-!
# From parsed TypeScript to the model's syntax

Trusted: the theorems are about the converted program, so this must map each
accepted source form to the model construct with the same JavaScript meaning.
It only drops spans and type annotations and refuses everything outside the
current level; it makes no typing decisions.
-/

namespace V2.Front
open Ariadne (Diagnostic Checked Span)

def unsupported (span : Span) (what : String) : Checked α :=
  throw { code := "A1001", message := s!"{what} is outside the supported subset (level L0)", span }

def convertUnary (span : Span) : String → Checked UnOp
  | "!" => pure .not
  | "-" => pure .neg
  | op => unsupported span s!"unary '{op}'"

def convertBinary (span : Span) : String → Checked BinOp
  | "+" => pure .add | "-" => pure .sub | "*" => pure .mul
  | "===" => pure .eq | "!==" => pure .ne
  | "<" => pure .lt | "<=" => pure .le | ">" => pure .gt | ">=" => pure .ge
  | "&&" => pure .and | "||" => pure .or
  | op => unsupported span s!"operator '{op}'"

def convertLiteral (span : Span) : Ariadne.Literal → Checked Lit
  | .boolean b => pure (.bool b)
  | .bigint n => pure (.bigint n)
  | .string units => pure (.string units)
  | .number .. => unsupported span "a number literal (use bigint)"
  | .undefined => unsupported span "undefined"
  | .null => unsupported span "null"

mutual
  def convertExpr : Ariadne.Expr → Checked Expr
    | .literal l span => return .lit (← convertLiteral span l)
    | .var x _ => pure (.var x)
    | .unary op e span => return .unary (← convertUnary span op) (← convertExpr e)
    | .binary op a b span => return .binary (← convertBinary span op) (← convertExpr a) (← convertExpr b)
    | .conditional c a b _ => return .cond (← convertExpr c) (← convertExpr a) (← convertExpr b)
    | .call (.var f _) args _ => return .call f (← convertExprs args)
    | e => unsupported e.span "this expression"

  def convertExprs : List Ariadne.Expr → Checked (List Expr)
    | [] => pure []
    | e :: es => return (← convertExpr e) :: (← convertExprs es)
end

mutual
  def convertStmt : Ariadne.Stmt → Checked Stmt
    | .let_ false x _ e _ => return .const x (← convertExpr e)
    | .return_ (.literal .undefined span) _ => unsupported span "a bare 'return'"
    | .return_ e _ => return .ret (← convertExpr e)
    | .if_ c yes no _ => return .ite (← convertExpr c) (← convertBranch yes) (← convertBranch no)
    | s => unsupported s.span "this statement"

  /-- An `if` branch: a braced block, or `else if`. -/
  def convertBranch : Ariadne.Stmt → Checked (List Stmt)
    | .block ss _ => convertStmts ss
    | .if_ c yes no _ => return [.ite (← convertExpr c) (← convertBranch yes) (← convertBranch no)]
    | s => unsupported s.span "this branch"

  def convertStmts : List Ariadne.Stmt → Checked (List Stmt)
    | [] => pure []
    | s :: ss => return (← convertStmt s) :: (← convertStmts ss)
end

def convertFunction (f : Ariadne.Function) : Checked Function := do
  if f.decreases.isSome then unsupported f.span "a termination measure"
  let .block body _ := f.body | unsupported f.span "this function body"
  return { name := f.name, params := f.params.map (·.name), body := ← convertStmts body }

/-- The model program for a parsed file, in source order. -/
def convertProgram (p : Ariadne.Program) : Checked Program := do
  if let some (name, _) := p.aliases.head? then unsupported {} s!"type alias '{name}'"
  if let some c := p.classes.head? then unsupported c.span "a class"
  p.functions.mapM convertFunction

end V2.Front

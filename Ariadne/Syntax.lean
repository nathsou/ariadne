import Ariadne.Source

namespace Ariadne

inductive Ty where
  | number | bigint | boolean | string | undefined | null | void
  | array (element : Ty)
  | map (key value : Ty)
  | tuple (elements : List Ty)
  | record (fields : List (String × Ty))
  | union (left right : Ty)
  | named (name : String)
  | function (params : List Ty) (result : Ty)
  deriving Repr, BEq, Inhabited

structure Param where
  name : String
  ty : Ty
  span : Span := {}
  deriving Repr, BEq, Inhabited

inductive Literal where
  | number (mantissa : Nat) (exponent : Int)
  | bigint (value : Int)
  | string (units : List UInt16)
  | boolean (value : Bool)
  | undefined | null
  deriving Repr, BEq, Inhabited

mutual
  inductive Expr where
    | literal (value : Literal) (span : Span)
    | var (name : String) (span : Span)
    | unary (op : String) (arg : Expr) (span : Span)
    | binary (op : String) (left right : Expr) (span : Span)
    | conditional (condition yes no : Expr) (span : Span)
    | call (callee : Expr) (args : List Expr) (span : Span)
    | member (object : Expr) (field : String) (span : Span)
    | index (object index : Expr) (span : Span)
    | array (elements : List Expr) (span : Span)
    | record (fields : List (String × Expr)) (span : Span)
    | lambda (params : List Param) (body : Stmt) (span : Span)
    | newMap (key value : Ty) (span : Span)
    deriving Repr, BEq, Inhabited

  inductive Stmt where
    | block (statements : List Stmt) (span : Span)
    | let_ (mutable : Bool) (name : String) (annotation : Option Ty)
        (value : Expr) (span : Span)
    | assign (target : Expr) (value : Expr) (span : Span)
    | expr (value : Expr) (span : Span)
    | if_ (condition : Expr) (yes no : Stmt) (span : Span)
    | while_ (condition : Expr) (body : Stmt) (span : Span)
    | for_ (init : Stmt) (condition : Expr) (update body : Stmt) (span : Span)
    | return_ (value : Expr) (span : Span)
    | break_ (span : Span)
    | continue_ (span : Span)
    deriving Repr, BEq, Inhabited
end

def Expr.span : Expr → Span
  | .literal _ s | .var _ s | .unary _ _ s | .binary _ _ _ s
  | .conditional _ _ _ s | .call _ _ s | .member _ _ s | .index _ _ s
  | .array _ s | .record _ s | .lambda _ _ s | .newMap _ _ s => s

def Stmt.span : Stmt → Span
  | .block _ s | .let_ _ _ _ _ s | .assign _ _ s | .expr _ s
  | .if_ _ _ _ s | .while_ _ _ s | .for_ _ _ _ _ s | .return_ _ s
  | .break_ s | .continue_ s => s

structure Function where
  name : String
  params : List Param
  result : Ty
  body : Stmt
  exported : Bool := false
  span : Span := {}
  deriving Repr, BEq, Inhabited

structure Program where
  functions : List Function
  aliases : List (String × Ty) := []
  deriving Repr, BEq, Inhabited

end Ariadne

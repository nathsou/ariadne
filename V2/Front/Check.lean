import V2.Front.Convert
import V2.Typed.Syntax

/-!
# Type checking and printing

Untrusted. Builds, as Lean source, the typed program whose erasure must equal the
converted AST, the readable definitions that must equal its denotation, and the
per-function source theorems. The kernel checks all of it when the generated file
is compiled, so a bug here makes that file fail to check; it cannot produce a
wrong theorem.
-/

namespace V2.Front
open V2.Parse (Diagnostic Checked Span)

def mismatch (span : Span) (message : String) : Checked α :=
  throw { code := "A2002", message, span }

def convertTy (span : Span) : Parse.Ty → Checked Ty
  | .boolean => pure .bool
  | .bigint => pure .int
  | .string => pure .string
  | _ => unsupported span "this type (L0 has boolean, bigint and string)"

def _root_.V2.Ty.ts : Ty → String
  | .bool => "boolean" | .int => "bigint" | .string => "string"

def _root_.V2.Ty.lean : Ty → String
  | .bool => "Bool" | .int => "Int" | .string => "JSString"

def _root_.V2.Ty.ctor : Ty → String
  | .bool => ".bool" | .int => ".int" | .string => ".string"

def _root_.V2.Ty.jsValue : Ty → String
  | .bool => ".bool" | .int => ".bigint" | .string => ".string"

def ident (x : String) : String := s!"«{x}»"

def leanString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | c => c.toString
  return out ++ "\""

/-- A JavaScript string literal: `js "…"` when every code unit is a printable BMP
character, else the code units. -/
def jsString (units : List UInt16) : String :=
  if units.all fun u => (u ≥ 0x20 && u < 0x7F) || (u ≥ 0xA0 && u < 0xD800) || (u ≥ 0xE000 && u < 0xFFFE) || u == 9 || u == 10 then
    s!"(js {leanString (String.ofList (units.map fun u => Char.ofNat u.toNat))})"
  else
    s!"({units.map fun u => s!"{u.toNat}"} : JSString)"

/-- Functions declared earlier, in source order. -/
structure FnSig where
  name : String
  params : List (String × Ty)
  result : Ty
  deriving Inhabited

structure Scope where
  fns : List FnSig
  /-- Bindings in scope, innermost first. -/
  locals : List (String × Ty)

/-- A checked expression as typed syntax, and as a readable Lean term. -/
structure Out where
  ty : Ty
  typed : String
  readable : String
  atomic : Bool := false

def Out.term (o : Out) : String := if o.atomic then o.readable else s!"({o.readable})"

def varPath : Nat → String
  | 0 => ".here"
  | n + 1 => s!"(.there (by decide) {varPath n})"

def fnPath : Nat → String
  | 0 => ".here"
  | n + 1 => s!"(.there {fnPath n})"

def unaryOut (span : Span) (op : String) (e : Out) : Checked Out :=
  match op, e.ty with
  | "!", .bool => pure { ty := .bool, typed := s!"(.not {e.typed})", readable := s!"!{e.term}" }
  | "-", .int => pure { ty := .int, typed := s!"(.neg {e.typed})", readable := s!"-{e.term}" }
  | op, τ => mismatch span s!"'{op}' does not apply to {τ.ts}"

def binaryOut (span : Span) (op : String) (a b : Out) : Checked Out := do
  let mk (ty : Ty) (ctor readable : String) : Out := { ty, typed := s!"(.{ctor} {a.typed} {b.typed})", readable }
  if a.ty != b.ty then mismatch span s!"'{op}' operands have types {a.ty.ts} and {b.ty.ts}"
  match op, a.ty with
  | "+", .int => pure (mk .int "add" s!"{a.term} + {b.term}")
  | "-", .int => pure (mk .int "sub" s!"{a.term} - {b.term}")
  | "*", .int => pure (mk .int "mul" s!"{a.term} * {b.term}")
  | "+", .string => pure (mk .string "concat" s!"{a.term} ++ {b.term}")
  | "===", _ => pure (mk .bool "eq" s!"{a.term} == {b.term}")
  | "!==", _ => pure (mk .bool "ne" s!"{a.term} != {b.term}")
  | "<", .int => pure (mk .bool "lt" s!"decide ({a.term} < {b.term})")
  | "<=", .int => pure (mk .bool "le" s!"decide ({a.term} ≤ {b.term})")
  | ">", .int => pure (mk .bool "gt" s!"decide ({a.term} > {b.term})")
  | ">=", .int => pure (mk .bool "ge" s!"decide ({a.term} ≥ {b.term})")
  | "<", .string => pure (mk .bool "slt" s!"strLt {a.term} {b.term}")
  | "<=", .string => pure (mk .bool "sle" s!"strLe {a.term} {b.term}")
  | ">", .string => pure (mk .bool "sgt" s!"strLt {b.term} {a.term}")
  | ">=", .string => pure (mk .bool "sge" s!"strLe {b.term} {a.term}")
  | "&&", .bool => pure (mk .bool "and" s!"{a.term} && {b.term}")
  | "||", .bool => pure (mk .bool "or" s!"{a.term} || {b.term}")
  | op, τ => mismatch span s!"'{op}' does not apply to {τ.ts}"

mutual
  def checkExpr (scope : Scope) : Parse.Expr → Checked Out
    | .literal (.boolean b) _ => pure { ty := .bool, typed := s!"(.bool {b})", readable := s!"{b}", atomic := true }
    | .literal (.bigint n) _ => pure { ty := .int, typed := s!"(.int {n})", readable := s!"({n} : Int)", atomic := true }
    | .literal (.string units) _ =>
      pure { ty := .string, typed := s!"(.str {jsString units})", readable := jsString units, atomic := true }
    | .literal _ span => unsupported span "this literal"
    | .var x span => do
      match scope.locals.findIdx? (·.1 == x) with
      | some i => pure { ty := scope.locals[i]!.2, typed := s!"(.var {varPath i})", readable := ident x, atomic := true }
      | none => throw { code := "A2001", message := s!"unknown variable '{x}'", span }
    | .unary op e span => do unaryOut span op (← checkExpr scope e)
    | .binary op a b span => do binaryOut span op (← checkExpr scope a) (← checkExpr scope b)
    | .conditional c a b span => do
      let c ← checkExpr scope c
      let a ← checkExpr scope a
      let b ← checkExpr scope b
      if c.ty != .bool then mismatch span "the condition must be a boolean"
      if a.ty != b.ty then mismatch span s!"the branches have types {a.ty.ts} and {b.ty.ts}"
      pure { ty := a.ty, typed := s!"(.cond {c.typed} {a.typed} {b.typed})",
             readable := s!"if {c.readable} then {a.readable} else {b.readable}" }
    | .call (.var f _) args span => do
      let some j := scope.fns.findIdx? (·.name == f)
        | throw { code := "A2001", message := s!"'{f}' is not a function declared earlier", span }
      let sig := scope.fns[j]!
      let args ← checkArgs scope args
      if args.length != sig.params.length then
        mismatch span s!"'{f}' takes {sig.params.length} arguments"
      for (a, (_, τ)) in args.zip sig.params do
        if a.ty != τ then mismatch span s!"argument of type {a.ty.ts} where {τ.ts} is expected"
      let typedArgs := args.foldr (fun a acc => s!"(.cons {a.typed} {acc})") ".nil"
      let readable := if args.isEmpty then ident f else
        " ".intercalate (ident f :: args.map (·.term))
      pure { ty := sig.result, typed := s!"(.call {fnPath (scope.fns.length - 1 - j)} {typedArgs})", readable,
             atomic := args.isEmpty }
    | e => unsupported e.span "this expression"

  def checkArgs (scope : Scope) : List Parse.Expr → Checked (List Out)
    | [] => pure []
    | e :: es => return (← checkExpr scope e) :: (← checkArgs scope es)
end

/-- A checked statement list: typed syntax, a readable printer taking the
continuation's text, and whether every path returns. -/
structure Block where
  typed : String
  readable : (indent : String) → (k : String) → String
  returns : Bool

def blockNil : Block := { typed := ".nil", readable := fun _ k => k, returns := false }

instance : Inhabited Block := ⟨blockNil⟩

def declare (scope : Scope) (span : Span) (x : String) (τ : Ty) : Checked Scope := do
  if scope.locals.any (·.1 == x) || scope.fns.any (·.name == x) then
    throw { code := "A2004", message := s!"'{x}' shadows a declaration in scope", span,
            help := some "Rename it: the model requires names in scope to be distinct." }
  pure { scope with locals := (x, τ) :: scope.locals }

mutual
  partial def checkStmts (scope : Scope) (result : Ty) : List Parse.Stmt → Checked Block
    | [] => pure blockNil
    | .let_ false x annotation e span :: rest => do
      let v ← checkExpr scope e
      if let some a := annotation then
        if (← convertTy span a) != v.ty then mismatch span s!"'{x}' is declared {(← convertTy span a).ts}"
      let rest ← checkStmts (← declare scope span x v.ty) result rest
      pure { typed := s!"(.const {leanString x} {v.typed}\n  {rest.typed})",
             readable := fun i k => s!"let {ident x} := {v.readable}\n{i}{rest.readable i k}",
             returns := rest.returns }
    | .return_ (.literal .undefined span) _ :: _ => unsupported span "a bare 'return'"
    | .return_ e span :: rest => do
      let v ← checkExpr scope e
      if v.ty != result then mismatch span s!"returns {v.ty.ts} where {result.ts} is expected"
      let rest ← checkStmts scope result rest
      pure { typed := s!"(.ret {v.typed} {rest.typed})", readable := fun _ _ => v.readable, returns := true }
    | .if_ c yes no span :: rest => do
      let c ← checkExpr scope c
      if c.ty != .bool then mismatch span "the condition must be a boolean"
      let yes ← checkBranch scope result yes
      let no ← checkBranch scope result no
      let rest ← checkStmts scope result rest
      pure { typed := s!"(.ite {c.typed}\n  {yes.typed}\n  {no.typed}\n  {rest.typed})",
             readable := fun i k =>
               let j := i ++ "  "
               let r := rest.readable j k
               s!"if {c.readable} then\n{j}{yes.readable j r}\n{i}else\n{j}{no.readable j r}",
             returns := (yes.returns && no.returns) || rest.returns }
    | s :: _ => unsupported s.span "this statement"

  partial def checkBranch (scope : Scope) (result : Ty) : Parse.Stmt → Checked Block
    | .block ss _ => checkStmts scope result ss
    | s@(.if_ ..) => checkStmts scope result [s]
    | s => unsupported s.span "this branch"
end

structure CheckedFn where
  sig : FnSig
  body : Block

def checkFunction (fns : List FnSig) (f : Parse.Function) : Checked CheckedFn := do
  if fns.any (·.name == f.name) then
    throw { code := "A2004", message := s!"'{f.name}' is declared twice", span := f.span }
  let result ← convertTy f.span f.result
  let mut scope : Scope := { fns, locals := [] }
  let mut params := []
  for p in f.params do
    let τ ← convertTy p.span p.ty
    params := params ++ [(p.name, τ)]
    -- Parameters are bound in order; lookups find the first, as the evaluator's do.
    if scope.locals.any (·.1 == p.name) || fns.any (·.name == p.name) || p.name == f.name then
      throw { code := "A2004", message := s!"'{p.name}' shadows a declaration in scope", span := p.span }
    scope := { scope with locals := scope.locals ++ [(p.name, τ)] }
  let .block body _ := f.body | unsupported f.span "this function body"
  let block ← checkStmts scope result body
  if !block.returns then
    throw { code := "A2003", message := s!"'{f.name}' may finish without returning a value", span := f.span }
  pure { sig := { name := f.name, params, result }, body := block }

def checkProgram (p : Parse.Program) : Checked (List CheckedFn) := do
  let mut fns := []
  let mut out := []
  for f in p.functions do
    let c ← checkFunction fns f
    fns := fns ++ [c.sig]
    out := out ++ [c]
  pure out

/-! ## Printing -/

def printLit : Lit → String
  | .bool b => s!"(.bool {b})"
  | .bigint n => s!"(.bigint {n})"
  | .string s => s!"(.string {jsString s})"

def printUnOp : UnOp → String
  | .not => ".not" | .neg => ".neg"

def printBinOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .eq => ".eq" | .ne => ".ne"
  | .lt => ".lt" | .le => ".le" | .gt => ".gt" | .ge => ".ge" | .and => ".and" | .or => ".or"

partial def printExpr : Expr → String
  | .lit l => s!"(.lit {printLit l})"
  | .var x => s!"(.var {leanString x})"
  | .unary op e => s!"(.unary {printUnOp op} {printExpr e})"
  | .binary op a b => s!"(.binary {printBinOp op} {printExpr a} {printExpr b})"
  | .cond c a b => s!"(.cond {printExpr c} {printExpr a} {printExpr b})"
  | .call f args => s!"(.call {leanString f} [{", ".intercalate (args.map printExpr)}])"

partial def printStmt (indent : String) : Stmt → String
  | .const x e => s!".const {leanString x} {printExpr e}"
  | .ret e => s!".ret {printExpr e}"
  | .ite c yes no =>
    let j := indent ++ "  "
    let list (ss : List Stmt) := if ss.isEmpty then "[]" else
      s!"[\n{j}  " ++ s!",\n{j}  ".intercalate (ss.map (printStmt (j ++ "  "))) ++ "]"
    s!".ite {printExpr c}\n{j}{list yes}\n{j}{list no}"

def printFunction (fn : Function) : String :=
  let body := ",\n      ".intercalate (fn.body.map (printStmt "      "))
  s!"\{ name := {leanString fn.name}, params := {fn.params.map leanString}, body := [\n      {body}] }"

def printCtx (ps : List (String × Ty)) : String :=
  "[" ++ ", ".intercalate (ps.map fun (x, τ) => s!"({leanString x}, {τ.ctor})") ++ "]"

def sigName (f : String) : String := s!"sig.{ident f}"

/-- The Lean source for a checked file: the AST, the typed program, readable
definitions, and per-function source theorems. -/
def printFile (source namespace_ : String) (ast : Program) (fns : List CheckedFn) : String := Id.run do
  -- A line comment: a path may contain `/-`, which would open a block comment.
  let name := ((source.splitOn "/").getLast?.getD source).map fun c => if c == '\n' || c == '\r' then ' ' else c
  let mut out := s!"import V2.Proof.Adequacy\n\n-- Generated by ariadne2 from {name}. Do not edit.\n\n"
  out := out ++ s!"namespace {namespace_}\nopen V2\n\nset_option maxRecDepth 4096\n\n"
  out := out ++ "/-- The source file in the model's syntax. -/\ndef ast : Program := [\n  " ++
    ",\n  ".intercalate (ast.map printFunction) ++ "]\n\n"
  for fn in fns do
    let s := fn.sig
    out := out ++ s!"def {sigName s.name} : Sig := \{ name := {leanString s.name}, " ++
      s!"params := {printCtx s.params}, result := {s.result.ctor} }\n"
  out := out ++ "\n"
  let mut earlier : List String := []
  for fn in fns do
    let s := fn.sig
    let φ := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
    out := out ++ s!"def body.{ident s.name} : TStmts {φ} {sigName s.name}.params {sigName s.name}.result :=\n  " ++
      fn.body.typed ++ "\n\n"
    earlier := s.name :: earlier
  let all := "[" ++ ", ".intercalate (earlier.map sigName) ++ "]"
  let program := fns.foldl (fun acc fn => s!"(.cons {sigName fn.sig.name} body.{ident fn.sig.name} {acc})") ".nil"
  out := out ++ s!"abbrev sigs : Sigs := {all}\n\ndef typed : TProgram sigs :=\n  {program}\n\n"
  out := out ++ "theorem erased : typed.erase = ast := by kernel_rfl\n\ntheorem wf : typed.WF := by decide +kernel\n\n"
  out := out ++ "/-! ## Readable definitions -/\n\n"
  for fn in fns do
    let s := fn.sig
    let params := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {τ.lean})")
    out := out ++ s!"def {ident s.name} {params} : {s.result.lean} :=\n  " ++
      fn.body.readable "  " (match s.result with | .bool => "false" | .int => "0" | .string => "[]") ++ "\n\n"
  out := out ++ "/-! ## Denotation

Each body is checked against its readable definition with the earlier functions'
readable definitions as its environment, so no check unfolds a callee. -/\n\n"
  let tupleOf (names : List String) : String :=
    "(" ++ ", ".intercalate (names.map (s!"{ident ·}.uncurried") ++ ["()"]) ++ ")"
  let mut prior : List String := []
  for fn in fns do
    let s := fn.sig
    let projections := (List.range s.params.length).map fun k =>
      "xs" ++ String.join (List.replicate k ".2") ++ ".1"
    let applied := if s.params.isEmpty then ident s.name else " ".intercalate (ident s.name :: projections)
    out := out ++ s!"def {ident s.name}.uncurried : {sigName s.name}.denote := fun xs => {applied}\n\n"
    out := out ++ s!"theorem {ident s.name}.body_eq :\n    body.{ident s.name}.denoteFn {tupleOf prior} = {ident s.name}.uncurried := by\n  kernel_rfl\n\n"
    prior := s.name :: prior
  let proof := fns.foldl (fun acc fn => s!"(TProgram.denote_cons {acc} {ident fn.sig.name}.body_eq)") "rfl"
  out := out ++ s!"theorem denote_eq : typed.denote = {tupleOf prior} :=\n  {proof}\n\n"
  out := out ++ "/-! ## Source theorems -/\n\n"
  let n := fns.length
  for (fn, i) in fns.zipIdx do
    let s := fn.sig
    let path := fnPath (n - 1 - i)
    let fvar := s!"({path} : FVar sigs {leanString s.name} {sigName s.name})"
    let binders := " ".intercalate (s.params.map fun (x, τ) => s!"({ident x} : {τ.lean})")
    let names := " ".intercalate (s.params.map (ident ·.1))
    let tuple := "(" ++ ", ".intercalate (s.params.map (ident ·.1) ++ ["()"]) ++ ")"
    let tuple := if s.params.isEmpty then "()" else tuple
    let call := if s.params.isEmpty then ident s.name else s!"{ident s.name} {names}"
    let encoded := "[" ++ ", ".intercalate (s.params.map fun (x, τ) => s!"{τ.jsValue} {ident x}") ++ "]"
    out := out ++ s!"/-- Every run of `{s.name}` converges to the readable definition's result. -/\n"
    out := out ++ s!"theorem {ident s.name}.source {binders} :\n    Converges (fun fuel' => run ast fuel' {leanString s.name} {encoded}) (.ok ({s.result.jsValue} ({call}))) :=\n"
    out := out ++ s!"  source_of erased wf denote_eq {fvar} {tuple}\n\n"
  out := out ++ s!"end {namespace_}\n"
  return out

/-- Parse, convert and check a TypeScript file, returning the generated Lean source. -/
def translate (source namespace_ text : String) : Checked String := do
  let parsed ← Parse.parse text
  let ast ← convertProgram parsed
  let fns ← checkProgram parsed
  pure (printFile source namespace_ ast fns)

end V2.Front

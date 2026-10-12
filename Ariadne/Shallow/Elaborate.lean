import Ariadne.Check
import Ariadne.Shallow.Denote

namespace Ariadne.Shallow.Elaborate
open Core

abbrev Context := List (String × Core.Ty)
abbrev Types (ctx : Context) := ctx.map Prod.snd
abbrev Typed (ctx : Context) := (t : Core.Ty) × Term (Types ctx) t

def refusal (code message : String) (span : Span) : Checked α :=
  .error { code, message, span, help := some "Use certify for the operational path. See docs/SHALLOW-PROGRESS.md for extraction coverage." }

def type (p : Program) (ty : Ariadne.Ty) (span : Span) : Checked Core.Ty := do
  let ty ← Check.resolve 100 p ty
  convert 100 ty
where
  convert : Nat → Ariadne.Ty → Checked Core.Ty
    | 0, _ => refusal "A5101" "type nesting budget exhausted" span
    | _ + 1, .void | _ + 1, .undefined => .ok .unit
    | _ + 1, .bigint => .ok .int
    | _ + 1, .number => .ok .number
    | _ + 1, .boolean => .ok .bool
    | _ + 1, .string | _ + 1, .stringLiteral _ => .ok .string
    | n + 1, .union t .undefined => return .option (← convert n t)
    | _, _ => refusal "A5102" "this type does not yet have an extraction representation" span

def lookup : (ctx : Context) → String → Option ((t : Core.Ty) × Var (Types ctx) t)
  | [], _ => none
  | (name, ty) :: ctx, wanted =>
    if name == wanted then some ⟨ty, .here⟩
    else (lookup ctx wanted).map fun ⟨t, v⟩ => ⟨t, .there v⟩

def cast (t : Core.Ty) (value : Typed ctx) (span : Span) : Checked (Term (Types ctx) t) :=
  if h : value.1 = t then .ok (h ▸ value.2)
  else refusal "A5102" "expression requires an unsupported type conversion" span

def coerce (t : Core.Ty) (value : Typed ctx) (span : Span) : Checked (Term (Types ctx) t) :=
  if h : value.1 = t then .ok (h ▸ value.2)
  else match t with
  | .option inner => do
    if value.1 == .unit then return .none
    return .some (← cast inner value span)
  | _ => refusal "A5102" "expression requires an unsupported type conversion" span

def arithmetic (op : String) (a b : Typed ctx) (span : Span) : Checked (Typed ctx) := do
  match a with
  | ⟨.int, a⟩ =>
    let b ← cast .int b span
    match op with
    | "+" => return ⟨.int, .binary .intAdd a b⟩
    | "-" => return ⟨.int, .binary .intSub a b⟩
    | "*" => return ⟨.int, .binary .intMul a b⟩
    | "===" => return ⟨.bool, .binary .intEq a b⟩
    | "!==" => return ⟨.bool, .unary .not (.binary .intEq a b)⟩
    | "<" => return ⟨.bool, .binary .intLt a b⟩
    | "<=" => return ⟨.bool, .binary .intLe a b⟩
    | ">" => return ⟨.bool, .binary .intLt b a⟩
    | ">=" => return ⟨.bool, .binary .intLe b a⟩
    | _ => refusal "A5104" "bigint division/remainder need safety obligations" span
  | ⟨.number, a⟩ =>
    let b ← cast .number b span
    match op with
    | "+" => return ⟨.number, .binary .numAdd a b⟩
    | "-" => return ⟨.number, .binary .numSub a b⟩
    | "*" => return ⟨.number, .binary .numMul a b⟩
    | "/" => return ⟨.number, .binary .numDiv a b⟩
    | "%" => return ⟨.number, .binary .numMod a b⟩
    | "===" => return ⟨.bool, .binary .numEq a b⟩
    | "!==" => return ⟨.bool, .unary .not (.binary .numEq a b)⟩
    | "<" => return ⟨.bool, .binary .numLt a b⟩
    | "<=" => return ⟨.bool, .binary .numLe a b⟩
    | ">" => return ⟨.bool, .binary .numLt b a⟩
    | ">=" => return ⟨.bool, .binary .numLe b a⟩
    | _ => refusal "A5104" "unsupported number operator" span
  | ⟨.string, a⟩ =>
    let b ← cast .string b span
    match op with
    | "+" => return ⟨.string, .binary .strAppend a b⟩
    | "===" => return ⟨.bool, .binary .strEq a b⟩
    | "!==" => return ⟨.bool, .unary .not (.binary .strEq a b)⟩
    | "<" => return ⟨.bool, .binary .strLt a b⟩
    | "<=" => return ⟨.bool, .binary .strLe a b⟩
    | ">" => return ⟨.bool, .binary .strLt b a⟩
    | ">=" => return ⟨.bool, .binary .strLe b a⟩
    | _ => refusal "A5104" "unsupported string operator" span
  | ⟨.bool, a⟩ =>
    let b ← cast .bool b span
    match op with
    | "&&" => return ⟨.bool, .ite a b (.bool false)⟩
    | "||" => return ⟨.bool, .ite a (.bool true) b⟩
    | "===" => return ⟨.bool, .binary .boolEq a b⟩
    | "!==" => return ⟨.bool, .unary .not (.binary .boolEq a b)⟩
    | _ => refusal "A5104" "unsupported boolean operator" span
  | ⟨.option _, a⟩ =>
    if b.1 == .unit && (op == "===" || op == "!==") then
      let some_ := Term.unary .isSome a
      return ⟨.bool, if op == "!==" then some_ else .unary .not some_⟩
    refusal "A5104" "only an undefined comparison is supported on options" span
  | _ => refusal "A5104" "unsupported scalar operation" span

mutual
  def expression (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) : Checked (Typed ctx) := do
    match fuel with
    | 0 => refusal "A5101" "expression nesting budget exhausted" expr.span
    | n + 1 =>
      match expr with
      | .literal (.bigint v) _ => return ⟨.int, .int v⟩
      | .literal (.number m e) _ => return ⟨.number, .number m e⟩
      | .literal (.boolean v) _ => return ⟨.bool, .bool v⟩
      | .literal (.string v) _ => return ⟨.string, .string v⟩
      | .literal .undefined _ => return ⟨.unit, .unit⟩
      | .var name span =>
        let some ⟨t, v⟩ := lookup ctx name | refusal "A5104" "unknown or unsupported intrinsic" span
        return ⟨t, .var v⟩
      | .unary op arg span =>
        let a ← expression p n ctx arg
        match op, a with
        | "!", ⟨.bool, a⟩ => return ⟨.bool, .unary .not a⟩
        | "-", ⟨.int, a⟩ => return ⟨.int, .unary .intNeg a⟩
        | "-", ⟨.number, a⟩ => return ⟨.number, .unary .numNeg a⟩
        | "+", ⟨.number, a⟩ => return ⟨.number, a⟩
        | _, _ => refusal "A5104" "unsupported unary operation" span
      | .binary "??" a b span =>
        let ⟨.option t, a⟩ ← expression p n ctx a
          | refusal "A5102" "nullish extraction requires an option" span
        let b ← asType p n ctx b t
        return ⟨t, .optionCase a b (.var .here)⟩
      | .binary op a b span => arithmetic op (← expression p n ctx a) (← expression p n ctx b) span
      | .conditional c a b _ =>
        let c ← asType p n ctx c .bool
        let ⟨t, a⟩ ← expression p n ctx a
        let b ← asType p n ctx b t
        return ⟨t, .ite c a b⟩
      | .call (.var name _) args span =>
        if !name.startsWith "#join" then refusal "A5104" "function calls have no shallow lowering yet" span
        let some ⟨.fn domain result, v⟩ := lookup ctx name
          | refusal "A5102" "invalid generated continuation" span
        return ⟨result, .app (.var v) (← tupleArgs p n ctx domain args span)⟩
      | .lambda _ _ span => refusal "A5104" "callback lowering is not implemented yet" span
      | _ => refusal "A5104" "this expression has no shallow model yet" expr.span

  def asType (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) (t : Core.Ty) :
      Checked (Term (Types ctx) t) := do
    match fuel with
    | 0 => refusal "A5101" "expression nesting budget exhausted" expr.span
    | n + 1 =>
      if let .conditional c a b _ := expr then
        return .ite (← asType p n ctx c .bool) (← asType p n ctx a t) (← asType p n ctx b t)
      coerce t (← expression p n ctx expr) expr.span
  def tupleArgs (p : Program) (fuel : Nat) (ctx : Context) (t : Core.Ty) (args : List Expr)
      (span : Span) : Checked (Term (Types ctx) t) :=
    match fuel with
    | 0 => refusal "A5101" "continuation argument budget exhausted" span
    | n + 1 => match t, args with
      | .unit, [] => .ok .unit
      | .pair a b, x :: xs => do
        return .pair (← asType p n ctx x a) (← tupleArgs p n ctx b xs span)
      | _, _ => refusal "A5102" "invalid continuation argument tuple" span

end

/-- Mutable locals become shadowed pure lets. Branches carry their continuations;
loops and calls are explicitly refused until their lowering has landed. -/
def statements (p : Program) : Nat → (ctx : Context) → List Stmt → (t : Core.Ty) →
    Checked (Term (Types ctx) t)
  | 0, _, _, _ => refusal "A5101" "statement nesting budget exhausted" {}
  | _ + 1, _, [], .unit => .ok .unit
  | _ + 1, _, [], _ => refusal "A5101" "extraction requires a return on every path" {}
  | n + 1, ctx, stmt :: rest, t => do
    match stmt with
    | .block ss _ => statements p n ctx (ss ++ rest) t
    | .let_ _ name annotation value _ =>
      let ⟨a, value⟩ ← match annotation with
        | none => expression p n ctx value
        | some ty => do
          let a ← type p ty value.span
          let value ← asType p n ctx value a
          pure ⟨a, value⟩
      return .let_ name value (← statements p n ((name, a) :: ctx) rest t)
    | .assign (.var name _) value span =>
      let some ⟨a, _⟩ := lookup ctx name | refusal "A5102" "unknown assignment target" span
      let value ← asType p n ctx value a
      return .let_ name value (← statements p n ((name, a) :: ctx) rest t)
    | .if_ c a b span =>
      if rest.isEmpty then
        return .ite (← asType p n ctx c .bool)
          (← statements p n ctx [a] t) (← statements p n ctx [b] t)
      let continuation ← statements p n ctx rest t
      let name := s!"#join{n}"
      let domain := Core.environmentType (Types ctx)
      let inner := (name, Core.Ty.fn domain t) :: ctx
      let jump : Stmt := .return_ (.call (.var name span)
        (ctx.map fun (name, _) => .var name span) span) span
      return .let_ "join" continuation.abstract
        (.ite (← asType p n inner c .bool)
          (← statements p n inner [a, jump] t) (← statements p n inner [b, jump] t))
    | .return_ value _ => asType p n ctx value t
    | .expr e _ =>
      let ⟨a, value⟩ ← expression p n ctx e
      return .let_ "ignored" value (← statements p n (("#ignored", a) :: ctx) rest t)
    | .while_ .. | .for_ .. | .forOf .. | .measured .. =>
      refusal "A5101" "loop extraction is not implemented yet" stmt.span
    | _ => refusal "A5102" "this statement needs ownership or control-flow lowering" stmt.span

def function (p : Program) (name : String) : Checked Core.Function := do
  if p.aliases.any (·.1 == "Int53") then
    refusal "A5104" "Int53 extraction requires range obligations, which are not implemented yet" {}
  let some f := p.functions.find? (·.name == name)
    | refusal "A5101" "unknown extraction entry point" {}
  let ctx ← f.params.mapM fun param => return (param.name, ← type p param.ty param.span)
  let result ← type p f.result f.span
  return { params := Types ctx, result, body := ← statements p 512 ctx [f.body] result }

end Ariadne.Shallow.Elaborate

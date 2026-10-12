import Ariadne.Check
import Ariadne.Shallow.Denote

namespace Ariadne.Shallow.Elaborate
open Core

structure Binding where
  name : String
  ty : Core.Ty
  declared : Core.Ty

abbrev Context := List Binding
abbrev Types (ctx : Context) := ctx.map Binding.ty
abbrev Typed (ctx : Context) := (t : Core.Ty) × Term (Types ctx) t

def binding (name : String) (ty : Core.Ty) : Binding := { name, ty, declared := ty }

def refined (ctx : Context) (name : String) (ty : Core.Ty) : Binding :=
  { name, ty, declared := ((ctx.find? (·.name == name)).map Binding.declared).getD ty }

/-- Continuations capture each live source binding once. Assignments invalidate
type refinements, just as in the frontend checker. -/
def afterWrites (ctx : Context) (writes : List String) : Context :=
  ctx.foldl (fun out b => if out.any (·.name == b.name) then out else
    out ++ [if writes.contains b.name then { b with ty := b.declared } else b]) []

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
    | n + 1, .union .undefined t => return .option (← convert n t)
    | n + 1, .readonly t | n + 1, .fieldReadonly t => convert n t
    | n + 1, .array t => return .list (← convert n t)
    | _, _ => refusal "A5102" "this type does not yet have an extraction representation" span

def lookup : (ctx : Context) → String → Option ((t : Core.Ty) × Var (Types ctx) t)
  | [], _ => none
  | b :: ctx, wanted =>
    if b.name == wanted then some ⟨b.ty, .here⟩
    else (lookup ctx wanted).map fun ⟨t, v⟩ => ⟨t, .there v⟩

def sourceType : Core.Ty → Ariadne.Ty
  | .unit => .undefined
  | .bool => .boolean
  | .int => .bigint
  | .number => .number
  | .string => .string
  | .option t => .union (sourceType t) .undefined
  | .list t => .array (sourceType t)
  | .pair a b => .tuple [sourceType a, sourceType b]
  | .fn a b => .function [sourceType a] (sourceType b)
  | .step .. | .exit .. => .void -- Internal control types are never source bindings.

def functionType : List Core.Ty → Core.Ty → Core.Ty
  | [], result => result
  | a :: rest, result => .fn a (functionType rest result)

def callbackResult (p : Program) (fuel : Nat) (ctx : Context) (fn : Expr) : Checked Core.Ty := do
  let .lambda params body span := fn | refusal "A5104" "expected a literal callback" fn.span
  let bindings ← (params.mapM fun param => do
    return ({ name := param.name, ty := ← Check.resolve 100 p param.ty, mutable := true } : Check.Binding))
  let captured := ctx.map fun b => ({ name := b.name, ty := sourceType b.ty, declared := some (sourceType b.declared), mutable := true } : Check.Binding)
  let result ← Check.inferCallback fuel { program := p, bindings := bindings ++ captured } body
  type p result span

def expressionResult (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) : Checked Core.Ty := do
  let bindings := ctx.map fun b => ({ name := b.name, ty := sourceType b.ty, declared := some (sourceType b.declared), mutable := true } : Check.Binding)
  type p (← Check.infer fuel { program := p, bindings } expr) expr.span

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
  | ⟨.unit, _⟩ =>
    if b.1 == .unit && (op == "===" || op == "!==") then return ⟨.bool, .bool (op == "===")⟩
    refusal "A5104" "unsupported undefined operation" span
  | _ => refusal "A5104" "unsupported scalar operation" span

/-- Convert exits in one loop to typed control constructors. Nested loop exits
belong to that nested loop; source returns still leave the enclosing function. -/
def loopControl (fuel : Nat) (retName nextName stopName : String) (state : Context)
    (canBreak canContinue : Bool) (stmt : Stmt) : Stmt :=
  match fuel with
  | 0 => stmt
  | n + 1 =>
    let recur := loopControl n retName nextName stopName state canBreak canContinue
    let jump := fun name span => Stmt.return_ (.call (.var name span)
      (state.map fun b => .var b.name span) span) span
    match stmt with
    | .return_ value span => .return_ (.call (.var retName span) [value] span) span
    | .break_ span => if canBreak then jump stopName span else stmt
    | .continue_ span => if canContinue then jump nextName span else stmt
    | .block ss span => .block (ss.map recur) span
    | .if_ c a b span => .if_ c (recur a) (recur b) span
    | .forOf mutable name xs body span =>
      .forOf mutable name xs (loopControl n retName nextName stopName state false false body) span
    | .for_ init c update body span =>
      .for_ init c update (loopControl n retName nextName stopName state false false body) span
    | .while_ c body span =>
      .while_ c (loopControl n retName nextName stopName state false false body) span
    | .switch_ value cases span => .switch_ value (cases.map fun (label, ss) =>
        (label, ss.map (loopControl n retName nextName stopName state false canContinue))) span
    | .measured measure body span => .measured measure (recur body) span
    | _ => stmt

/-- A switch break leaves only the switch; nested loops and switches retain
control of their own breaks. -/
def switchControl : Nat → Stmt → Stmt → Stmt
  | 0, _, stmt => stmt
  | n + 1, jump, stmt => match stmt with
    | .break_ _ => jump
    | .block ss span => .block (ss.map (switchControl n jump)) span
    | .if_ c a b span => .if_ c (switchControl n jump a) (switchControl n jump b) span
    | .measured measure body span => .measured measure (switchControl n jump body) span
    | _ => stmt

def switchBreaks : Nat → Stmt → Bool
  | 0, _ => true
  | _ + 1, .break_ _ => true
  | n + 1, .block ss _ => ss.any (switchBreaks n)
  | n + 1, .if_ _ a b _ => switchBreaks n a || switchBreaks n b
  | n + 1, .measured _ body _ => switchBreaks n body
  | _, _ => false

def switchDispatch (value : Expr) (fallback : Stmt) : List (Option Expr × List Stmt) → Stmt
  | [] => fallback
  | (none, _) :: rest => switchDispatch value fallback rest
  | (some label, body) :: rest =>
    .if_ (.binary "===" value label label.span) (.block body label.span)
      (switchDispatch value fallback rest) label.span

def loopVariable : Var (a :: Γ) t → Term [Core.environmentType Γ, a] t
  | .here => .var (.there .here)
  | .there v => Core.project (.var .here) v

/-- Close a loop body over its element and explicit state tuple. -/
def abstractLoop (name : String) (body : Term (a :: Γ) t) :
    Term Δ (.fn a (.fn (Core.environmentType Γ) t)) :=
  .closed (.lam name (.lam "state" (body.substitute loopVariable)))

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
      | .binary "&&" _ _ span | .binary "||" _ _ span =>
        return ⟨.bool, ← condition p n ctx expr
          [.return_ (.literal (.boolean true) span) span]
          [.return_ (.literal (.boolean false) span) span] .bool⟩
      | .binary op a b span => arithmetic op (← expression p n ctx a) (← expression p n ctx b) span
      | .conditional c a b span =>
        let t ← expressionResult p n ctx expr
        return ⟨t, ← condition p n ctx c [.return_ a span] [.return_ b span] t⟩
      | .array xs span =>
        let some first := xs.head? | refusal "A5102" "empty arrays require a type annotation" span
        let element ← match first with
          | .spread e _ => do
            let ⟨.list t, _⟩ ← expression p n ctx e | refusal "A5102" "spread requires a list" span
            pure t
          | _ => (expression p n ctx first).map Sigma.fst
        return ⟨.list element, ← elements p n ctx element xs⟩
      | .member object "length" span =>
        let ⟨.list _, xs⟩ ← expression p n ctx object | refusal "A5104" "this length operation has no lowering" span
        return ⟨.number, .unary .length xs⟩
      | .index object index span =>
        let ⟨.list t, xs⟩ ← expression p n ctx object | refusal "A5102" "indexing requires a list" span
        return ⟨.option t, .binary .get xs (← asType p n ctx index .number)⟩
      | .call (.member object method _) args span =>
        let ⟨.list t, xs⟩ ← expression p n ctx object
          | refusal "A5104" "this method has no shallow lowering" span
        match method, args with
        | "map", [fn] =>
          let b ← callbackResult p n ctx fn
          return ⟨.list b, .listMap (← callback p n ctx [t, .number] b fn) xs⟩
        | "filter", [fn] => return ⟨.list t, .listFilter (← callback p n ctx [t, .number] .bool fn) xs⟩
        | "some", [fn] => return ⟨.bool, .listSome (← callback p n ctx [t, .number] .bool fn) xs⟩
        | "every", [fn] => return ⟨.bool, .listEvery (← callback p n ctx [t, .number] .bool fn) xs⟩
        | "find", [fn] => return ⟨.option t, .listFind (← callback p n ctx [t, .number] .bool fn) xs⟩
        | "findIndex", [fn] => return ⟨.number, .listFindIndex (← callback p n ctx [t, .number] .bool fn) xs⟩
        | "reduce", [fn, initial] =>
          let ⟨acc, initial⟩ ← expression p n ctx initial
          return ⟨acc, .listReduce (← callback p n ctx [acc, t, .number] acc fn) initial xs⟩
        | "slice", [] => return ⟨.list t, xs⟩
        | "slice", [start] => return ⟨.list t, .listSlice xs (← asType p n ctx start .number) (.unary .length xs)⟩
        | "slice", [start, stop] => return ⟨.list t, .listSlice xs (← asType p n ctx start .number) (← asType p n ctx stop .number)⟩
        | "toReversed", [] => return ⟨.list t, .unary .reverse xs⟩
        | "concat", args =>
          let mut result := xs
          for arg in args do
            let value ← expression p n ctx arg
            let list ← if value.1 == .list t then cast (.list t) value arg.span
              else (coerce t value arg.span).map (fun v => Term.cons v .nil)
            result := .binary .append result list
          return ⟨.list t, result⟩
        | _, _ => refusal "A5104" "this array method has no shallow lowering" span
      | .call (.var name _) args span =>
        if name.startsWith "#internal" then
          let some ⟨t, v⟩ := lookup ctx name
            | refusal "A5102" "invalid generated control function" span
          return ← applications p n ctx ⟨t, .var v⟩ args span
        if name.startsWith "#join" then
          let some ⟨.fn domain result, v⟩ := lookup ctx name
            | refusal "A5102" "invalid generated continuation" span
          return ⟨result, .app (.var v) (← tupleArgs p n ctx domain args span)⟩
        let some f := p.functions.find? (·.name == name)
          | refusal "A5104" "this intrinsic has no shallow lowering" span
        for param in f.params do
          let ty ← Check.resolve 100 p param.ty
          if Check.referenceType ty && !Check.immutable ty then
            refusal "A5102" "calls with mutable reference parameters need state threading" span
        let inputs ← f.params.mapM fun param => type p param.ty param.span
        let result ← type p f.result f.span
        let closed ← lambda p n [] inputs f.params result f.body
        applications p n ctx ⟨functionType inputs result, .closed closed⟩ args span
      | .lambda _ _ span => refusal "A5104" "callback lowering is not implemented yet" span
      | _ => refusal "A5104" "this expression has no shallow model yet" expr.span

  def asType (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) (t : Core.Ty) :
      Checked (Term (Types ctx) t) :=
    match fuel, t, expr with
    | 0, _, _ => refusal "A5101" "expression nesting budget exhausted" expr.span
    | n + 1, t, .conditional c a b _ => do
      condition p n ctx c [.return_ a a.span] [.return_ b b.span] t
    | n + 1, .list element, .array xs _ => elements p n ctx element xs
    | n + 1, t, expr => do coerce t (← expression p n ctx expr) expr.span
  def tupleArgs (p : Program) (fuel : Nat) (ctx : Context) (t : Core.Ty) (args : List Expr)
      (span : Span) : Checked (Term (Types ctx) t) :=
    match fuel with
    | 0 => refusal "A5101" "continuation argument budget exhausted" span
    | n + 1 => match t, args with
      | .unit, [] => .ok .unit
      | .pair a b, x :: xs => do
        return .pair (← asType p n ctx x a) (← tupleArgs p n ctx b xs span)
      | _, _ => refusal "A5102" "invalid continuation argument tuple" span

  def elements (p : Program) : Nat → (ctx : Context) → (t : Core.Ty) → List Expr → Checked (Term (Types ctx) (.list t))
    | 0, _, _, _ => refusal "A5101" "array element budget exhausted" {}
    | _ + 1, _, _, [] => .ok .nil
    | n + 1, ctx, t, x :: xs => do
      let rest ← elements p n ctx t xs
      match x with
      | .spread value _ => return .binary .append (← asType p n ctx value (.list t)) rest
      | _ => return .cons (← asType p n ctx x t) rest

  def callback (p : Program) (fuel : Nat) (ctx : Context) (inputs : List Core.Ty) (result : Core.Ty) (fn : Expr) :
      Checked (Term (Types ctx) (functionType inputs result)) := do
    match fuel with
    | 0 => refusal "A5101" "callback lowering budget exhausted" fn.span
    | n + 1 =>
      let .lambda params body _ := fn | refusal "A5104" "expected a literal callback" fn.span
      lambda p n ctx inputs params result body

  def lambda (p : Program) : Nat → (ctx : Context) → (inputs : List Core.Ty) → List Param → (result : Core.Ty) →
      Stmt → Checked (Term (Types ctx) (functionType inputs result))
    | 0, _, _, _, _, body => refusal "A5101" "callback or call lowering budget exhausted" body.span
    | n + 1, ctx, [], [], result, body => statements p n ctx [body] result
    | n + 1, ctx, a :: inputs, params, result, body => do
      let name ← match params.head? with
        | none => pure s!"#unused{inputs.length}"
        | some param => do
          let t ← type p param.ty param.span
          if t != a then refusal "A5102" "callback parameter type mismatch" param.span
          pure param.name
      return .lam name (← lambda p n (binding name a :: ctx) inputs params.tail result body)
    | _, _, _, _, _, body => refusal "A5102" "too many callback parameters" body.span

  def applications (p : Program) : Nat → (ctx : Context) → Typed ctx → List Expr → Span → Checked (Typed ctx)
    | 0, _, _, _, span => refusal "A5101" "call argument budget exhausted" span
    | _ + 1, _, value, [], _ => .ok value
    | n + 1, ctx, ⟨.fn a b, f⟩, x :: xs, span => do
      applications p n ctx ⟨b, .app f (← asType p n ctx x a)⟩ xs span
    | _, _, _, _, span => refusal "A5102" "too many function arguments" span

  /-- Guards refine optional bindings in the selected branch. The missing arm
  binds Unit, and the present arm binds the unwrapped native value. -/
  def condition (p : Program) : Nat → (ctx : Context) → Expr → List Stmt → List Stmt →
      (t : Core.Ty) → Checked (Term (Types ctx) t)
    | 0, _, guard, _, _, _ => refusal "A5101" "condition lowering budget exhausted" guard.span
    | n + 1, ctx, guard, yes, no, t => do
      match guard with
      | .unary "!" arg _ => condition p n ctx arg no yes t
      | .binary "&&" a b span =>
        condition p n ctx a [.if_ b (.block yes span) (.block no span) span] no t
      | .binary "||" a b span =>
        condition p n ctx a yes [.if_ b (.block yes span) (.block no span) span] t
      | .binary op (.var name _) (.literal .undefined _) _ =>
        if op == "===" || op == "!==" then
          if let some ⟨.option element, v⟩ := lookup ctx name then
            let missing := if op == "===" then yes else no
            let present := if op == "!==" then yes else no
            let absent ← statements p n (refined ctx name .unit :: ctx) missing t
            let present ← statements p n (refined ctx name element :: ctx) present t
            return .optionCase (.var v) (.let_ name .unit absent) present
        return .ite (← asType p n ctx guard .bool)
          (← statements p n ctx yes t) (← statements p n ctx no t)
      | _ =>
        return .ite (← asType p n ctx guard .bool)
          (← statements p n ctx yes t) (← statements p n ctx no t)


  /-- Mutable locals become shadowed pure lets. Branches share their continuations.
  Structural loops carry an explicit value state and typed exits. -/
  def statements (p : Program) : Nat → (ctx : Context) → List Stmt → (t : Core.Ty) →
      Checked (Term (Types ctx) t)
    | 0, _, _, _ => refusal "A5101" "statement nesting budget exhausted" {}
    | _ + 1, _, [], .unit => .ok .unit
    | _ + 1, _, [], _ => refusal "A5101" "extraction requires a return on every path" {}
    | n + 1, ctx, stmt :: rest, t => do
      match stmt with
      | .block ss span =>
        if rest.isEmpty || !ss.any (fun s => match s with | .let_ .. => true | _ => false) then
          return ← statements p n ctx (ss ++ rest) t
        let state := afterWrites ctx (Check.writes n stmt)
        let continuation ← statements p n state rest t
        let name := s!"#join{n}"
        let domain := Core.environmentType (Types state)
        let inner := binding name (.fn domain t) :: ctx
        let jump : Stmt := .return_ (.call (.var name span)
          (state.map fun b => .var b.name span) span) span
        return .let_ "join" continuation.abstract (← statements p n inner (ss ++ [jump]) t)
      | .let_ _ name annotation value _ =>
        let ⟨a, value⟩ ← match annotation with
          | none => expression p n ctx value
          | some ty => do
            let a ← type p ty value.span
            let value ← asType p n ctx value a
            pure ⟨a, value⟩
        return .let_ name value (← statements p n (binding name a :: ctx) rest t)
      | .assign (.var name _) value span =>
        let some target := ctx.find? (·.name == name) | refusal "A5102" "unknown assignment target" span
        let a := target.declared
        let value ← asType p n ctx value a
        return .let_ name value (← statements p n (binding name a :: ctx) rest t)
      | .if_ c a b span =>
        if rest.isEmpty then
          return ← condition p n ctx c [a] [b] t
        if Check.exits n a || Check.exits n b then
          return ← condition p n ctx c (a :: rest) (b :: rest) t
        let state := afterWrites ctx (Check.writes n stmt)
        let continuation ← statements p n state rest t
        let name := s!"#join{n}"
        let domain := Core.environmentType (Types state)
        let inner := binding name (Core.Ty.fn domain t) :: ctx
        let jump : Stmt := .return_ (.call (.var name span)
          (state.map fun b => .var b.name span) span) span
        return .let_ "join" continuation.abstract (← condition p n inner c [a, jump] [b, jump] t)
      | .return_ value _ => asType p n ctx value t
      | .expr e _ =>
        let ⟨a, value⟩ ← expression p n ctx e
        return .let_ "ignored" value (← statements p n (binding "#ignored" a :: ctx) rest t)
      | .switch_ value cases span =>
        if let some (_, fallback) := cases.find? (·.1.isNone) then
          if !cases.any (fun c => c.2.any (switchBreaks n)) then
            let ⟨a, value⟩ ← expression p n ctx value
            let saved := s!"#switch{n}"
            let dispatch := switchDispatch (.var saved span) (.block fallback span) cases
            return .let_ "switchValue" value
              (← statements p n (binding saved a :: ctx) [dispatch] t)
        let state := afterWrites ctx (Check.writes n stmt)
        let continuation ← statements p n state rest t
        let name := s!"#joinSwitch{n}"
        let domain := Core.environmentType (Types state)
        let jump : Stmt := .return_ (.call (.var name span)
          (state.map fun b => .var b.name span) span) span
        let cases := cases.map fun (label, body) =>
          (label, body.map (switchControl n jump))
        let fallback := match cases.find? (·.1.isNone) with
          | some (_, body) => Stmt.block body span
          | none => jump
        let ⟨a, value⟩ ← expression p n ctx value
        let saved := s!"#switch{n}"
        let inner := binding saved a :: binding name (.fn domain t) :: ctx
        let dispatch := switchDispatch (.var saved span) fallback cases
        return .let_ "joinSwitch" continuation.abstract
          (.let_ "switchValue" (value.rename Var.there) (← statements p n inner [dispatch] t))
      | .forOf _ name collection body span =>
        let ⟨.list a, xs⟩ ← expression p n ctx collection
          | refusal "A5102" "this collection has no loop lowering" span
        let state := afterWrites ctx (Check.writes n body)
        let stateType := Core.environmentType (Types state)
        let stepType := Core.Ty.step stateType t
        let retName := s!"#internalReturn{n}"
        let nextName := s!"#joinNext{n}"
        let stopName := s!"#joinStop{n}"
        let bodyCtx := binding name a :: state
        let retCtx := binding retName (.fn t stepType) :: bodyCtx
        let nextCtx := binding nextName (.fn stateType stepType) :: retCtx
        let inner := binding stopName (.fn stateType stepType) :: nextCtx
        let body := loopControl n retName nextName stopName state true true body
        let jump := Stmt.return_ (.call (.var nextName span)
          (state.map fun b => .var b.name span) span) span
        let body ← statements p n inner [body, jump] stepType
        let body := Term.let_ retName (.lam "result" (.ret (.var .here)))
          (.let_ nextName (.lam "state" (.next (.var .here)))
            (.let_ stopName (.lam "state" (.stop (.var .here))) body))
        let initial ← tupleArgs p n ctx stateType (state.map fun b => .var b.name span) span
        let continuation ← statements p n state rest t
        return .exitCase (.each xs initial (abstractLoop name body))
          continuation.abstract (.lam "result" (.var .here))
      | .for_ init guard update body span =>
        let .let_ _ name annotation start _ := init
          | refusal "A5101" "counted loops must declare their own counter" span
        let .binary "<" (.var tested _) stop _ := guard
          | refusal "A5101" "counted loops require an increasing half-open bound" span
        let .assign (.var updated _) (.binary "+" (.var prior _) (.literal (.bigint 1) _) _) _ := update
          | refusal "A5101" "this counter update needs Int53 safety or a termination measure" span
        if tested != name || updated != name || prior != name || (Check.writes n body).contains name then
          refusal "A5101" "only the update step may assign the counted-loop counter" span
        match stop with
        | .var bound _ =>
          if bound == name || (Check.writes n body).contains bound then
            refusal "A5101" "the counted-loop bound must be invariant" span
        | .literal (.bigint _) _ => pure ()
        | _ => refusal "A5101" "this counted-loop bound has no invariance check" span
        if let some ty := annotation then
          if (← type p ty span) != .int then refusal "A5101" "this counter needs Int53 safety" span
        let _ ← asType p n ctx start .int
        let _ ← asType p n ctx stop .int
        let rangeName := s!"#internalRange{n}"
        let rangeTy := Core.Ty.fn .int (.fn .int (.list .int))
        let range : Term (Types ctx) rangeTy := .lam "start" (.lam "stop"
          (.binary .intRange (.var (.there .here)) (.var .here)))
        let inner := binding rangeName rangeTy :: ctx
        let loop := Stmt.forOf true name (.call (.var rangeName span) [start, stop] span) body span
        return .let_ "range" range (← statements p n inner (loop :: rest) t)
      | .while_ .. | .measured .. =>
        refusal "A5101" "loop extraction is not implemented yet" stmt.span
      | _ => refusal "A5102" "this statement needs ownership or control-flow lowering" stmt.span

end

def function (p : Program) (name : String) : Checked Core.Function := do
  if p.aliases.any (·.1 == "Int53") then
    refusal "A5104" "Int53 extraction requires range obligations, which are not implemented yet" {}
  let some f := p.functions.find? (·.name == name)
    | refusal "A5101" "unknown extraction entry point" {}
  let ctx ← f.params.mapM fun param => return binding param.name (← type p param.ty param.span)
  let result ← type p f.result f.span
  return { params := Types ctx, result, body := ← statements p 512 ctx [f.body] result }

end Ariadne.Shallow.Elaborate

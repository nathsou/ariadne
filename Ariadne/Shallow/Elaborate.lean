import Ariadne.Check
import Ariadne.Shallow.Denote
import Ariadne.Shallow.Unions
import Ariadne.Shallow.ClassPlan

namespace Ariadne.Shallow.Elaborate
open Core

structure Binding where
  name : String
  ty : Core.Ty
  declared : Core.Ty
  owned : Bool := false
  loan : Option String := none

abbrev Context := List Binding
abbrev Types (ctx : Context) := ctx.map Binding.ty
abbrev Typed (ctx : Context) := (t : Core.Ty) × Term (Types ctx) t

def binding (name : String) (ty : Core.Ty) (owned : Bool := false) : Binding := { name, ty, declared := ty, owned }

def refined (ctx : Context) (name : String) (ty : Core.Ty) : Binding :=
  { name, ty, declared := ((ctx.find? (·.name == name)).map Binding.declared).getD ty,
    owned := ((ctx.find? (·.name == name)).map Binding.owned).getD false,
    loan := (ctx.find? (·.name == name)).bind Binding.loan }

/-- Continuations capture each live source binding once. Assignments invalidate
type refinements, just as in the frontend checker. -/
def afterWrites (ctx : Context) (writes : List String) : Context :=
  ctx.foldl (fun out b => if out.any (·.name == b.name) then out else
    out ++ [if writes.contains b.name then { b with ty := b.declared } else b]) []

def refusal (code message : String) (span : Span) : Checked α :=
  .error { code, message, span, help := some "Use certify for the operational path. See docs/SHALLOW-PROGRESS.md for extraction coverage." }

def collectionKey (ty : Ariadne.Ty) (span : Span) : Checked Core.Key :=
  match ty with
  | .bigint => .ok .int
  | .number => .ok .number
  | .string | .stringLiteral _ => .ok .string
  | .boolean => .ok .bool
  | _ => refusal "A5102" "collection keys require a scalar value representation" span

def type (p : Program) (ty : Ariadne.Ty) (span : Span) : Checked Core.Ty :=
  convert 100 ty
where
  convert : Nat → Ariadne.Ty → Checked Core.Ty
    | 0, _ => refusal "A5101" "type nesting budget exhausted" span
    | n + 1, .named name => do
      let name := if p.classes.any (·.name == name) then ClassPlan.stateName name else name
      let some source := p.aliases.lookup name | refusal "A5102" "unknown type alias" span
      match Check.unreadonly source with
      | .record _ => return .named (← Declarations.info p name span).declaration
      | .union a b =>
        if a != .undefined && b != .undefined then
          return .named (← Declarations.info p name span).declaration
        convert n source
      | _ => convert n source
    | _ + 1, .void | _ + 1, .undefined => .ok .unit
    | _ + 1, .bigint => .ok .int
    | _ + 1, .number => .ok .number
    | _ + 1, .boolean => .ok .bool
    | _ + 1, .string | _ + 1, .stringLiteral _ => .ok .string
    | n + 1, .union t .undefined => return .option (← convert n t)
    | n + 1, .union .undefined t => return .option (← convert n t)
    | n + 1, .readonly t | n + 1, .fieldReadonly t => convert n t
    | n + 1, .array t | n + 1, .iterator t => return .list (← convert n t)
    | n + 1, .tuple [a, b] => return .pair (← convert n a) (← convert n b)
    | n + 1, .map k v => return .map (← collectionKey (← Check.resolve 100 p k) span) (← convert n v)
    | _ + 1, .set k => return .set (← collectionKey (← Check.resolve 100 p k) span)
    | _, _ => refusal "A5102" "this type does not yet have an extraction representation" span

structure Prepared where
  ctx : Context
  result : Core.Ty
  body : Stmt
  loans : List Param

def prepare (p : Program) (fuel : Nat) (f : Ariadne.Function) : Checked Prepared := do
  let names ← StatePlan.effects p fuel f
  let loans := f.params.filter (fun param => names.contains param.name)
  let ctx ← f.params.mapM fun param => do
    let ty ← type p param.ty param.span
    let loan := if names.contains param.name then some (StatePlan.loanName param.name) else none
    return ({ name := param.name, ty, declared := ty, owned := names.contains param.name, loan } : Binding)
  let result ← type p f.result f.span
  if names.isEmpty then return ⟨ctx, result, f.body, []⟩
  let states ← loans.mapM fun param => type p param.ty param.span
  let endBody := if result == .unit then
    Stmt.block [f.body, .return_ (.literal .undefined f.span) f.span] f.span else f.body
  let body ← StatePlan.returns names fuel endBody
  let body := Stmt.block (names.map (fun name =>
    Stmt.let_ false (StatePlan.loanName name) none (.var name f.span) f.span) ++ [body]) f.span
  return ⟨ctx, .pair result (Core.environmentType states), body, loans⟩

def lookup : (ctx : Context) → String → Option ((t : Core.Ty) × Var (Types ctx) t)
  | [], _ => none
  | b :: ctx, wanted =>
    if b.name == wanted then some ⟨b.ty, .here⟩
    else (lookup ctx wanted).map fun ⟨t, v⟩ => ⟨t, .there v⟩

def lowerClassCall (p : Program) (ctx : Context) (expr : Expr) : Option Expr := do
  match expr with
  | .newClass name args span =>
    return .call (.var (ClassPlan.methodName name "#new") span) args span
  | .call (.member (.var owner ownerSpan) method _) args span =>
    let ⟨.named declaration, _⟩ ← lookup ctx owner | none
    let c ← p.classes.find? (fun c => ClassPlan.stateName c.name == declaration.name)
    if !(c.methods.any (·.name == method)) then none else
      return .call (.var (ClassPlan.methodName c.name method) span) (.var owner ownerSpan :: args) span
  | _ => none

def keySourceType : Core.Key → Ariadne.Ty
  | .int => .bigint
  | .number => .number
  | .string => .string
  | .bool => .boolean

def sourceType : Core.Ty → Ariadne.Ty
  | .unit => .undefined
  | .bool => .boolean
  | .int => .bigint
  | .number => .number
  | .string => .string
  | .option t => .union (sourceType t) .undefined
  | .list t => .array (sourceType t)
  | .map k v => .map (keySourceType k) (sourceType v)
  | .set k => .set (keySourceType k)
  | .pair a b => .tuple [sourceType a, sourceType b]
  | .sum a b => .union (sourceType a) (sourceType b)
  | .named declaration => .named declaration.name
  | .fn a b => .function [sourceType a] (sourceType b)
  | .step .. | .exit .. => .void -- Internal control types are never source bindings.

def functionType : List Core.Ty → Core.Ty → Core.Ty
  | [], result => result
  | a :: rest, result => .fn a (functionType rest result)

def callbackResult (p : Program) (fuel : Nat) (ctx : Context) (fn : Expr) : Checked Core.Ty := do
  let .lambda params body span := fn | refusal "A5104" "expected a literal callback" fn.span
  let bindings ← (params.mapM fun param => do
    return ({ name := param.name, ty := ← Check.resolve 100 p param.ty, mutable := true } : Check.Binding))
  let captured ← ctx.mapM fun b => do
    let ty ← Check.resolve 100 p (sourceType b.ty)
    let declared ← Check.resolve 100 p (sourceType b.declared)
    pure ({ name := b.name, ty, declared := some declared, mutable := true } : Check.Binding)
  let result ← Check.inferCallback fuel { program := p, bindings := bindings ++ captured } body
  type p result span

def expressionSource (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) : Checked Ariadne.Ty := do
  let bindings ← ctx.mapM fun b => do
    let ty ← Check.resolve 100 p (sourceType b.ty)
    let declared ← Check.resolve 100 p (sourceType b.declared)
    pure ({ name := b.name, ty, declared := some declared, mutable := true } : Check.Binding)
  Check.infer fuel { program := p, bindings } expr

def expressionResult (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) : Checked Core.Ty := do
  type p (← expressionSource p fuel ctx expr) expr.span

def cast (t : Core.Ty) (value : Typed ctx) (span : Span) : Checked (Term (Types ctx) t) :=
  if h : value.1 = t then .ok (h ▸ value.2)
  else refusal "A5102" "expression requires an unsupported type conversion" span

def coercePlain (t : Core.Ty) (value : Typed ctx) (span : Span) : Checked (Term (Types ctx) t) :=
  if h : value.1 = t then .ok (h ▸ value.2)
  else match t, value with
  | .named parent, ⟨.named child, value⟩ =>
    match Declarations.inject parent child (.unpack value) with
    | some payload => .ok (.pack parent payload)
    | none => refusal "A5102" "named value is not a view of the target declaration" span
  | _, _ => refusal "A5102" "expression requires an unsupported type conversion" span

def coerce (t : Core.Ty) (value : Typed ctx) (span : Span) : Checked (Term (Types ctx) t) :=
  if h : value.1 = t then .ok (h ▸ value.2)
  else match t with
  | .option inner => do
    if value.1 == .unit then return .none
    return .some (← coercePlain inner value span)
  | other => coercePlain other value span

def iterable (value : Typed ctx) (span : Span) : Checked (Typed ctx) :=
  match value with
  | ⟨.list t, xs⟩ => .ok ⟨.list t, xs⟩
  | ⟨.map k v, m⟩ => .ok ⟨.list (.pair k.type v), .unary .mapEntries m⟩
  | ⟨.set k, s⟩ => .ok ⟨.list k.type, .unary .setValues s⟩
  | _ => refusal "A5102" "this value has no iterable representation" span

def recordField (name : String) (span : Span) : List (String × Ariadne.Ty) → Typed ctx → Checked (Typed ctx)
  | (field, source) :: fields, ⟨.pair a b, value⟩ =>
    if name == field then
      match Declarations.fixedString source with
      | some literal => .ok ⟨.string, .string literal⟩
      | none => .ok ⟨a, .fst value⟩
    else recordField name span fields ⟨b, .snd value⟩
  | _, _ => refusal "A5102" "unknown field or invalid named record shape" span


def replaceRecordField (name : String) (span : Span) (replacement : Typed ctx) :
    List (String × Ariadne.Ty) → (payload : Typed ctx) → Checked (Term (Types ctx) payload.1)
  | (field, source) :: fields, ⟨.pair a b, value⟩ => do
    if name == field then
      if (Declarations.fixedString source).isSome then
        refusal "A5102" "literal fields cannot be updated" span
      return .pair (← cast a replacement span) (.snd value)
    return .pair (.fst value) (← replaceRecordField name span replacement fields ⟨b, .snd value⟩)
  | _, _ => refusal "A5102" "unknown field or invalid record update" span
termination_by structural fields _ => fields

def replaceField (p : Program) (ctx : Context) (owner field : String) (value : Typed ctx) (span : Span) : Checked (Typed ctx) := do
  let some ⟨.named declaration, index⟩ := lookup ctx owner
    | refusal "A5102" "field updates require a named record owner" span
  let fields ← Declarations.record p declaration span
  let updated ← replaceRecordField field span value fields ⟨_, .unpack (.var index)⟩
  return ⟨.named declaration, .pack declaration updated⟩

def packSubstitution (Γ : List Core.Ty) (child : Named.Declaration) :
    Core.Substitution (.named child :: Γ) (shapeType child.shape :: Γ) :=
  fun v => match v with
    | .here => .pack child (.var .here)
    | .there v => .var (.there v)

def variantBody (ctx : Context) (name : String) (child : Named.Declaration)
    (body : Term (Types (refined ctx name (.named child) :: ctx)) t) :
    Term (shapeType child.shape :: Types ctx) t :=
  body.substitute (packSubstitution (Types ctx) child)

def canonicalField : Nat → (ctx : Context) → Ariadne.Ty → Typed ctx → String → Span → Checked (Typed ctx)
  | 0, _, _, _, _, span => refusal "A5101" "union field nesting budget exhausted" span
  | n + 1, ctx, source, payload, name, span => do
    match Check.unreadonly source, payload with
    | .record fields, payload => recordField name span fields payload
    | .union left right, ⟨.sum a b, payload⟩ =>
      let ⟨result, leftBody⟩ ← canonicalField n (binding "#payload" a :: ctx) left ⟨a, .var .here⟩ name span
      let rightBody ← canonicalField n (binding "#payload" b :: ctx) right ⟨b, .var .here⟩ name span
      return ⟨result, .sumCase payload leftBody (← cast result rightBody span)⟩
    | _, _ => refusal "A5102" "this named value has no common record field" span


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
      if let some lowered := lowerClassCall p ctx expr then
        return ← expression p n ctx lowered
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
      | .newMap key value span =>
        let .map k v ← type p (.map key value) span | refusal "A5102" "invalid Map type" span
        return ⟨.map k v, .mapEmpty⟩
      | .newSet key span =>
        let .set k ← type p (.set key) span | refusal "A5102" "invalid Set type" span
        return ⟨.set k, .setEmpty⟩
      | .array xs span =>
        let some first := xs.head? | refusal "A5102" "empty arrays require a type annotation" span
        let element ← match first with
          | .spread e _ => do
            let ⟨.list t, _⟩ ← iterable (← expression p n ctx e) span | refusal "A5102" "spread requires a list" span
            pure t
          | _ => (expression p n ctx first).map Sigma.fst
        return ⟨.list element, ← elements p n ctx element xs⟩
      | .member object field span =>
        match ← expression p n ctx object with
        | ⟨.named declaration, value⟩ =>
          canonicalField n ctx (← Declarations.info p declaration.name span).source ⟨_, .unpack value⟩ field span
        | ⟨.list _, xs⟩ =>
          if field == "length" then return ⟨.number, .unary .length xs⟩
          refusal "A5104" "this array property has no lowering" span
        | ⟨.pair _ _, _⟩ =>
          if field == "length" then return ⟨.number, .number 2 0⟩
          refusal "A5104" "this tuple property has no lowering" span
        | ⟨.map _ _, m⟩ =>
          if field == "size" then return ⟨.number, .unary .mapSize m⟩
          refusal "A5104" "this Map property has no lowering" span
        | ⟨.set _, s⟩ =>
          if field == "size" then return ⟨.number, .unary .setSize s⟩
          refusal "A5104" "this Set property has no lowering" span
        | _ => refusal "A5104" "this property has no shallow lowering" span
      | .index object index span =>
        match ← expression p n ctx object with
        | ⟨.list t, xs⟩ => return ⟨.option t, .binary .get xs (← asType p n ctx index .number)⟩
        | ⟨.pair a b, pair⟩ =>
          match index with
          | .literal (.number 0 0) _ => return ⟨a, .fst pair⟩
          | .literal (.number 1 0) _ => return ⟨b, .snd pair⟩
          | _ => refusal "A5102" "pair indices must be 0 or 1" span
        | _ => refusal "A5102" "indexing requires a list or pair" span
      | .call (.member object method _) args span =>
        match ← expression p n ctx object with
        | ⟨.map k v, m⟩ =>
          match method, args with
          | "get", [key] => return ⟨.option v, .binary .mapGet m (← asType p n ctx key k.type)⟩
          | "has", [key] => return ⟨.bool, .binary .mapHas m (← asType p n ctx key k.type)⟩
          | "keys", [] => return ⟨.list k.type, .unary .mapKeys m⟩
          | "values", [] => return ⟨.list v, .unary .mapValues m⟩
          | "entries", [] => return ⟨.list (.pair k.type v), .unary .mapEntries m⟩
          | _, _ => refusal "A5104" "this Map method needs statement-level state lowering" span
        | ⟨.set k, s⟩ =>
          match method, args with
          | "has", [key] => return ⟨.bool, .binary .setHas s (← asType p n ctx key k.type)⟩
          | "keys", [] | "values", [] => return ⟨.list k.type, .unary .setValues s⟩
          | "entries", [] => return ⟨.list (.pair k.type k.type), .unary .setEntries s⟩
          | _, _ => refusal "A5104" "this Set method needs statement-level state lowering" span
        | ⟨.list t, xs⟩ =>
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
        | _ => refusal "A5104" "this method has no shallow lowering" span
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
        if !(← StatePlan.effects p n f).isEmpty then
          refusal "A5102" "this effectful call needs statement-level state threading" span
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
    | n + 1, .option inner, .record fields span =>
      return .some (← asType p n ctx (.record fields span) inner)
    | n + 1, .named declaration, .record fields span => do
      for (name, value) in fields do
        if name == "" then refusal "A5102" "named record spread is not lowered yet" span
        -- Check overwritten and erased initializers as well as retained fields.
        let _ ← expression p n ctx value
      let fields := fields.foldl (fun out (name, value) =>
        (out.filter (·.1 != name)) ++ [(name, value)]) []
      if let some (left, right) ← Declarations.union p declaration span then
        let source ← expressionSource p n ctx (.record fields span)
        let child ← if Check.compatible source left.source then pure left else
          if Check.compatible source right.source then pure right else
          refusal "A5102" "record initializer does not select a union variant" span
        let value ← asType p n ctx (.record fields span) (.named child.declaration)
        return ← coercePlain (.named declaration) ⟨.named child.declaration, value⟩ span
      let target ← Declarations.record p declaration span
      return .pack declaration (← cast (Core.shapeType declaration.shape)
        (← recordValue p n ctx fields target span) span)
    | n + 1, .list element, .array xs _ => elements p n ctx element xs
    | n + 1, .pair a b, .array [x, y] _ => do return .pair (← asType p n ctx x a) (← asType p n ctx y b)
    | n + 1, t, expr => do coerce t (← expression p n ctx expr) expr.span
  def recordValue (p : Program) : Nat → (ctx : Context) → List (String × Expr) →
      List (String × Ariadne.Ty) → Span → Checked (Typed ctx)
    | 0, _, _, _, span => refusal "A5101" "record construction nesting budget exhausted" span
    | _ + 1, _, _, [], _ => .ok ⟨.unit, .unit⟩
    | n + 1, ctx, values, (name, source) :: fields, span => do
      let ⟨tailType, tail⟩ ← recordValue p n ctx values fields span
      let value := (values.lookup name).getD (.literal .undefined span)
      if (Declarations.fixedString source).isSome then
        return ⟨.pair .unit tailType, .pair .unit tail⟩
      let fieldType := Core.shapeType (← Declarations.shape span 100 source)
      return ⟨.pair fieldType tailType, .pair (← asType p n ctx value fieldType) tail⟩

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
      | .spread value _ => return .binary .append (← cast (.list t) (← iterable (← expression p n ctx value) value.span) value.span) rest
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
      | .binary op (.member (.var name _) field _) (.literal (.string tag) _) span =>
        if op == "===" || op == "!==" then
          if let some ⟨.named declaration, v⟩ := lookup ctx name then
            if let some (left, right) ← Declarations.union p declaration span then
              let payload ← cast (.sum (shapeType left.declaration.shape) (shapeType right.declaration.shape))
                ⟨_, .unpack (.var v)⟩ span
              return .sumCase payload
                (← unionArm p n ctx name left field tag (op == "===") guard yes no t)
                (← unionArm p n ctx name right field tag (op == "===") guard yes no t)
            if let .record fields := Check.unreadonly (← Declarations.info p declaration.name span).source then
              if let some source := fields.lookup field then
                if let some actual := Declarations.fixedString source then
                  return ← statements p n ctx (if (actual == tag) == (op == "===") then yes else no) t
        return .ite (← asType p n ctx guard .bool)
          (← statements p n ctx yes t) (← statements p n ctx no t)
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

  def unionArm (p : Program) : Nat → (ctx : Context) → String → (child : Declarations.Info) →
      String → JSString → Bool → Expr → List Stmt → List Stmt → (t : Core.Ty) →
      Checked (Term (shapeType child.declaration.shape :: Types ctx) t)
    | 0, _, _, _, _, _, _, guard, _, _, _ => refusal "A5101" "union narrowing budget exhausted" guard.span
    | n + 1, ctx, name, child, field, tag, positive, guard, yes, no, t => do
      let inner := refined ctx name (.named child.declaration) :: ctx
      let body ← match Check.unreadonly child.source with
        | .record fields => do
          let some source := fields.lookup field | refusal "A5102" "union variant lacks the discriminant" guard.span
          let some actual := Declarations.fixedString source
            | refusal "A5102" "union narrowing requires fixed literal discriminants" guard.span
          statements p n inner (if (actual == tag) == positive then yes else no) t
        | .union .. => condition p n inner guard yes no t
        | _ => refusal "A5102" "only tagged record unions support narrowing" guard.span
      return variantBody ctx name child.declaration body


  def localMutation (p : Program) (fuel : Nat) (ctx : Context) (expr : Expr) :
      Checked (Option (String × Typed ctx)) := do
    match fuel with
    | 0 => refusal "A5101" "mutation lowering budget exhausted" expr.span
    | n + 1 =>
      if let .call (.var restore _) [value] span := expr then
        if restore.startsWith "#restore:" then
          let name := restore.drop 9 |>.toString
          let some target := ctx.find? (·.name == name) | refusal "A5102" "unknown restored owner" span
          if !target.owned then refusal "A5102" "call mutation needs an exclusive owner" span
          return some (name, ⟨target.ty, ← asType p n ctx value target.ty⟩)
      if let .call (.var "#field" _) [.member (.var owner _) field _, value] span := expr then
        let some target := ctx.find? (·.name == owner) | refusal "A5102" "unknown field owner" span
        if !target.owned then refusal "A5102" "field update needs exclusive ownership" span
        let expected ← expression p n ctx (.member (.var owner span) field span)
        let value ← asType p n ctx value expected.1
        return some (owner, ← replaceField p ctx owner field ⟨expected.1, value⟩ span)
      let .call (.member receiver method _) args span := expr | return none
      if !StatePlan.mutator method then return none
      let (name, field) ← match receiver with
        | .var name _ => pure (name, none)
        | .member (.var name _) field _ => pure (name, some field)
        | _ => refusal "A5102" "nested collection mutation requires backward functions" span
      let some target := ctx.find? (·.name == name) | refusal "A5102" "unknown mutation target" span
      if !target.owned then refusal "A5102" "mutating a borrowed parameter requires a returned state component" span
      let some ⟨ty, index⟩ := lookup ctx name | refusal "A5102" "unknown mutation target" span
      let collection ← match field with
        | none => pure (⟨ty, .var index⟩ : Typed ctx)
        | some field => expression p n ctx (.member (.var name span) field span)
      let updated ← match collection, method, args with
        | ⟨.map k v, collection⟩, "set", [key, value] => do
          pure ⟨.map k v, .mapSet collection (← asType p n ctx key k.type) (← asType p n ctx value v)⟩
        | ⟨.map k v, collection⟩, "delete", [key] => do
          pure ⟨.map k v, .binary .mapDelete collection (← asType p n ctx key k.type)⟩
        | ⟨.map k v, _⟩, "clear", [] => pure ⟨.map k v, .mapEmpty⟩
        | ⟨.set k, collection⟩, "add", [key] => do
          pure ⟨.set k, .binary .setAdd collection (← asType p n ctx key k.type)⟩
        | ⟨.set k, collection⟩, "delete", [key] => do
          pure ⟨.set k, .binary .setDelete collection (← asType p n ctx key k.type)⟩
        | ⟨.set k, _⟩, "clear", [] => pure ⟨.set k, .setEmpty⟩
        | ⟨.list a, collection⟩, "push", [value] => do
          pure ⟨.list a, .binary .append collection (.cons (← asType p n ctx value a) .nil)⟩
        | _, _, _ => refusal "A5104" "this mutation has no native state operation" span
      let updated ← match field with
        | none => pure updated
        | some field => replaceField p ctx name field updated span
      return some (name, updated)

  /-- Mutable locals become shadowed pure lets. Branches share their continuations.
  Structural loops carry an explicit value state and typed exits. -/
  def statements (p : Program) : Nat → (ctx : Context) → List Stmt → (t : Core.Ty) →
      Checked (Term (Types ctx) t)
    | 0, _, _, _ => refusal "A5101" "statement nesting budget exhausted" {}
    | _ + 1, _, [], .unit => .ok .unit
    | _ + 1, _, [], _ => refusal "A5101" "extraction requires a return on every path" {}
    | n + 1, ctx, stmt :: rest, t => do
      let sourceValue := match stmt with
        | .let_ _ _ _ value _ | .expr value _ | .return_ value _ => some value
        | .assign (.var ..) value _ => some value
        | _ => none
      if let some lowered := sourceValue.bind (lowerClassCall p ctx) then
        let stmt := match stmt with
          | .let_ m name ty _ span => .let_ m name ty lowered span
          | .expr _ span => .expr lowered span
          | .return_ _ span => .return_ lowered span
          | .assign target _ span => .assign target lowered span
          | other => other
        return ← statements p n ctx (stmt :: rest) t
      let value := match stmt with
        | .let_ _ _ _ value _ | .expr value _ | .return_ value _ => some value
        | .assign (.var ..) value _ => some value
        | _ => none
      if let some (.call (.var name _) args span) := value then
        if let some f := p.functions.find? (·.name == name) then
          let prepared ← prepare p n f
          if !prepared.loans.isEmpty then
            let body ← statements p n prepared.ctx [prepared.body] prepared.result
            let call := Term.app body.abstract (← tupleArgs p n ctx (Core.environmentType (Types prepared.ctx)) args span)
            let package := s!"#borrowedCall{n}"
            let component := fun (base : Expr) (index : Nat) => Expr.index base (.literal (.number index 0) span) span
            let root := Expr.var package span
            let sourceResult := component root 0
            let states := component root 1
            let mut restores : List Stmt := []
            for (param, i) in prepared.loans.zipIdx do
              let some (_, argument) := (f.params.zip args).find? (·.1.name == param.name)
                | refusal "A5102" "invalid borrowed call arguments" span
              match argument with
              | .var owner _ =>
                let state := component ((List.range i).foldl (fun value _ => component value 1) states) 0
                restores := restores ++ [.expr (.call (.var ("#restore:" ++ owner) span) [state] span) span]
              | _ =>
                if !Check.fresh argument then refusal "A5102" "nested borrowed arguments need backward functions" argument.span
            let resumed := match stmt with
              | .let_ mutable name annotation _ span => .let_ mutable name annotation sourceResult span
              | .expr _ span => .expr sourceResult span
              | .return_ _ span => .return_ sourceResult span
              | .assign target _ span => .assign target sourceResult span
              | other => other
            return .let_ package call
              (← statements p n (binding package prepared.result :: ctx) (restores ++ resumed :: rest) t)
      match stmt with
      | .block ss span =>
        if Check.exits n stmt then return ← statements p n ctx ss t
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
        let restoredResult := match value with
          | .index (.var package _) (.literal (.number 0 0) _) _ => package.startsWith "#borrowedCall"
          | _ => false
        let owns := Check.fresh value || restoredResult
        let ⟨a, value⟩ ← match annotation with
          | none => expression p n ctx value
          | some ty => do
            let a ← type p ty value.span
            let value ← asType p n ctx value a
            pure ⟨a, value⟩
        return .let_ name value (← statements p n (binding name a owns :: ctx) rest t)
      | .assign (.member (.var owner _) field _) value span =>
        statements p n ctx (.expr (.call (.var "#field" span) [.member (.var owner span) field span, value] span) span :: rest) t
      | .assign (.var name _) value span =>
        let some target := ctx.find? (·.name == name) | refusal "A5102" "unknown assignment target" span
        if target.loan.isSome then
          refusal "A5102" "reassigning a mutated borrowed parameter requires conditional loan tracking" span
        let a := target.declared
        let owns := Check.fresh value
        let value ← asType p n ctx value a
        return .let_ name value (← statements p n (binding name a owns :: ctx) rest t)
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
        if let some (name, ⟨a, value⟩) ← localMutation p n ctx e then
          let target := (ctx.find? (·.name == name)).getD (binding name a true)
          let inner := ({ name, ty := a, declared := target.declared, owned := true, loan := target.loan } : Binding) :: ctx
          if let some loan := target.loan then
            return .let_ name value (.let_ loan (.var .here)
              (← statements p n (binding loan a :: inner) rest t))
          return .let_ name value (← statements p n inner rest t)
        let ⟨a, value⟩ ← expression p n ctx e
        return .let_ "ignored" value (← statements p n (binding "#ignored" a :: ctx) rest t)
      | .switch_ value cases span =>
        let direct := match value with
          | .member (.var name _) _ _ => match lookup ctx name with
            | some ⟨.named ⟨_, .sum ..⟩, _⟩ => true
            | _ => false
          | _ => false
        if let some (_, fallback) := cases.find? (·.1.isNone) then
          if !cases.any (fun c => c.2.any (switchBreaks n)) then
            if direct then
              return ← statements p n ctx [switchDispatch value (.block fallback span) cases] t
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
        if direct then
          return .let_ "joinSwitch" continuation.abstract
            (← statements p n (binding name (.fn domain t) :: ctx) [switchDispatch value fallback cases] t)
        let ⟨a, value⟩ ← expression p n ctx value
        let saved := s!"#switch{n}"
        let inner := binding saved a :: binding name (.fn domain t) :: ctx
        let dispatch := switchDispatch (.var saved span) fallback cases
        return .let_ "joinSwitch" continuation.abstract
          (.let_ "switchValue" (value.rename Var.there) (← statements p n inner [dispatch] t))
      | .forOf _ name collection body span =>
        let ⟨.list a, xs⟩ ← iterable (← expression p n ctx collection) span
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
  let p ← ClassPlan.lower p
  let p ← Declarations.withVariants p
  let some f := p.functions.find? (·.name == name)
    | refusal "A5101" "unknown extraction entry point" {}
  let prepared ← prepare p 512 f
  let body ← statements p 512 prepared.ctx [prepared.body] prepared.result
  return { params := Types prepared.ctx, result := prepared.result, body }

end Ariadne.Shallow.Elaborate

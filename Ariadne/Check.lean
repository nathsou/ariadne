import Ariadne.Parser

namespace Ariadne
namespace Check

structure Binding where
  name : String
  ty : Ty
  mutable : Bool
  borrowed : Bool := false
  readOnly : Bool := false
  declared : Option Ty := none
  span : Span := {}
  deriving Repr

structure Context where
  program : Program
  bindings : List Binding := []
  result : Ty := .void
  loopDepth : Nat := 0
  switchDepth : Nat := 0
  currentClass : Option String := none
  /-- Collection roots protected while a callback runs. -/
  protectedRoots : List String := []
  /-- Callbacks may not call user functions until interprocedural effects are available. -/
  inCallback : Bool := false
  pureCallback : Bool := true
  /-- First callback pass discovers the result; the second checks every return. -/
  inferReturns : Bool := false

def error (code message : String) (span : Span) (help : Option String := none) : Checked α :=
  .error { code, message, span, help }

def resolve (fuel : Nat) (p : Program) (ty : Ty) : Checked Ty := do
  match fuel with
  | 0 => error "A2001" "cyclic or excessively nested type alias" {}
  | n + 1 =>
    match ty with
    | .named name =>
      if p.classes.any (·.name == name) then return .class_ name
      let some t := p.aliases.lookup name | error "A2001" s!"unknown type '{name}'" {}
      resolve n p t
    | .array t => return .array (← resolve n p t)
    | .set t => return .set (← resolve n p t)
    | .iterator t => return .iterator (← resolve n p t)
    | .readonly t => return .readonly (← resolve n p t)
    | .fieldReadonly t => return .fieldReadonly (← resolve n p t)
    | .map k v => return .map (← resolve n p k) (← resolve n p v)
    | .union a b => return .union (← resolve n p a) (← resolve n p b)
    | .record fs => return .record (← fs.mapM fun (k, v) => return (k, ← resolve n p v))
    | .tuple ts => return .tuple (← ts.mapM (resolve n p))
    | .function ps r => return .function (← ps.mapM (resolve n p)) (← resolve n p r)
    | t => return t

def typeName : Ty → String
  | .number => "number" | .bigint => "bigint" | .boolean => "boolean"
  | .string => "string" | .undefined => "undefined" | .null => "null" | .void => "void"
  | .array t => typeName t ++ "[]"
  | .set t => s!"Set<{typeName t}>"
  | .iterator t => s!"iterator<{typeName t}>"
  | .readonly t | .fieldReadonly t => "readonly " ++ typeName t
  | .stringLiteral units => reprStr units
  | .class_ name => name
  | .map k v => s!"Map<{typeName k}, {typeName v}>"
  | .union a b => s!"{typeName a} | {typeName b}"
  | .tuple _ => "tuple" | .record _ => "record" | .function _ _ => "callback"
  | .named n => n

def referenceType : Ty → Bool
  | .array _ | .map _ _ | .set _ | .iterator _ | .class_ _ | .record _ | .tuple _ | .function _ _ => true
  | .readonly t | .fieldReadonly t => referenceType t
  | .union a b => referenceType a || referenceType b
  | _ => false

def unreadonly : Ty → Ty
  | .readonly t | .fieldReadonly t => unreadonly t
  | t => t

def immutableFuel : Nat → Ty → Bool
  | 0, _ => false
  | _ + 1, .number | _ + 1, .bigint | _ + 1, .boolean | _ + 1, .string
  | _ + 1, .stringLiteral _ | _ + 1, .undefined | _ + 1, .null | _ + 1, .void => true
  | n + 1, .union a b => immutableFuel n a && immutableFuel n b
  | n + 1, .record fs => fs.all fun (_, t) => match t with | .fieldReadonly t => immutableFuel n t | _ => false
  | n + 1, .readonly (.array t) | n + 1, .readonly (.set t) => immutableFuel n t
  | n + 1, .readonly (.map k v) => immutableFuel n k && immutableFuel n v
  | n + 1, .readonly t | n + 1, .fieldReadonly t => immutableFuel n t
  | _, _ => false

def immutable (t : Ty) : Bool := immutableFuel 100 t

def supportedTypeFuel : Nat → Ty → Bool
  | 0, _ => false
  | n + 1, .array t | n + 1, .readonly t | n + 1, .fieldReadonly t => supportedTypeFuel n t
  | _ + 1, .set t => !referenceType t
  | n + 1, .map k v => !referenceType k && supportedTypeFuel n v
  | n + 1, .record fields => fields.all (fun p => supportedTypeFuel n p.2)
  | n + 1, .tuple ts => ts.all (supportedTypeFuel n)
  | n + 1, .union a b => supportedTypeFuel n a && supportedTypeFuel n b
  | _ + 1, .function .. | _ + 1, .iterator .. => false
  | _, _ => true

def supportedType (t : Ty) : Bool := supportedTypeFuel 100 t

def requireSupportedType (ty : Ty) (span : Span) : Checked Unit :=
  if supportedType ty then .ok ()
  else error "A3001" "collection keys must be scalar and stored types cannot be callbacks" span

def compatibleFuel : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, actual, expected => actual == expected || match actual, expected with
    | .readonly a, .readonly b => compatibleFuel n a b
    | .fieldReadonly a, b => compatibleFuel n a b
    | a, .readonly b | a, .fieldReadonly b => compatibleFuel n a b
    | .union a b, t => compatibleFuel n a t && compatibleFuel n b t
    | t, .union a b => compatibleFuel n t a || compatibleFuel n t b
    | .stringLiteral _, .string => true
    | .array a, .array b | .set a, .set b => compatibleFuel n a b
    | .record actual, .record expected => expected.all fun (key, t) =>
        compatibleFuel n ((actual.lookup key).getD .undefined) t
    | .tuple actual, .tuple expected => actual.length == expected.length &&
        (actual.zip expected).all fun (a, b) => compatibleFuel n a b
    | .undefined, .void => true
    | _, _ => false

def compatible (actual expected : Ty) : Bool := compatibleFuel 100 actual expected

def requireType (actual expected : Ty) (span : Span) : Checked Unit :=
  if compatible actual expected then .ok ()
  else error "A2002" s!"expected {typeName expected}, found {typeName actual}" span

def binding (ctx : Context) (name : String) (span : Span) : Checked Binding :=
  match ctx.bindings.find? (fun b => b.name == name) with
  | some b => .ok b
  | none => error "A2003" s!"unknown name '{name}'" span

def root : Expr → Option String
  | .var n _ => some n
  | .member e _ _ | .index e _ _ => root e
  | .call (.member e method _) _ _ => if ["keys", "values", "entries"].contains method then root e else none
  | _ => none

def fresh : Expr → Bool
  | .array .. | .record .. | .newMap .. | .newSet .. | .newClass .. => true
  | .call (.var ..) _ _ => true
  | .call (.member _ method _) _ _ => ["map", "filter", "slice", "concat", "toReversed", "toSorted", "entries", "keys", "values"].contains method
  | _ => false

/-- Container reads are shared loans, never additional owners. -/
def sharedRead : Expr → Bool
  | .index .. => true
  | .call (.member _ "get" _) _ _ | .call (.member _ "find" _) _ _ => true
  | .binary "??" a b _ => sharedRead a && (fresh b || sharedRead b)
  | _ => false

def scalarPrintable : Ty → Bool
  | .number | .bigint | .string | .stringLiteral _ | .boolean | .null | .undefined => true
  | .union a b => scalarPrintable a && scalarPrintable b
  | _ => false

/-- Possible ways to leave a statement. Sequential composition follows only the
normal path, so an unreachable return cannot hide a preceding break. -/
structure Flow where
  normal : Bool := false
  returned : Bool := false
  broken : Bool := false
  continued : Bool := false

def Flow.alternative (a b : Flow) : Flow :=
  ⟨a.normal || b.normal, a.returned || b.returned,
    a.broken || b.broken, a.continued || b.continued⟩

def Flow.sequence (a b : Flow) : Flow :=
  if a.normal then { a with normal := false }.alternative b else a

def flow : Nat → Stmt → Flow
  | 0, _ => { normal := true }
  | _ + 1, .return_ .. => { returned := true }
  | _ + 1, .break_ .. => { broken := true }
  | _ + 1, .continue_ .. => { continued := true }
  | n + 1, .block ss _ => ss.foldl (fun out stmt => out.sequence (flow n stmt)) { normal := true }
  | n + 1, .if_ _ a b _ => (flow n a).alternative (flow n b)
  | n + 1, .switch_ _ cases span =>
    let branches := cases.foldl (fun (out : Flow) c => out.alternative (flow n (.block c.2 span)))
      { normal := !cases.any (·.1.isNone) }
    { branches with normal := branches.normal || branches.broken, broken := false }
  | n + 1, .while_ _ body _ | n + 1, .for_ _ _ _ body _ | n + 1, .forOf _ _ _ body _ =>
    { normal := true, returned := (flow n body).returned }
  | n + 1, .measured _ body _ => flow n body
  | _, _ => { normal := true }

def exits (fuel : Nat) (stmt : Stmt) : Bool := !(flow fuel stmt).normal

def filterType (p : Ty → Bool) : Ty → Option Ty
  | .union a b => match filterType p a, filterType p b with
    | some a, some b => some (.union a b)
    | some a, none => some a
    | none, some b => some b
    | none, none => none
  | t => if p t then some t else none

mutual
  def writesExpr : Nat → Expr → List String
    | 0, _ => []
    | n + 1, .lambda _ body _ => writes n body
    | n + 1, .call e args _ => writesExpr n e ++ args.flatMap (writesExpr n)
    | n + 1, .binary _ a b _ => writesExpr n a ++ writesExpr n b
    | n + 1, .conditional c a b _ => writesExpr n c ++ writesExpr n a ++ writesExpr n b
    | n + 1, .unary _ a _ | n + 1, .member a _ _ | n + 1, .spread a _ => writesExpr n a
    | n + 1, .index a b _ => writesExpr n a ++ writesExpr n b
    | n + 1, .array es _ | n + 1, .newClass _ es _ => es.flatMap (writesExpr n)
    | n + 1, .record fs _ => fs.flatMap (fun f => writesExpr n f.2)
    | _, _ => []

  def writes : Nat → Stmt → List String
    | 0, _ => []
    | n + 1, .assign target value _ => (root target).toList ++ writesExpr n value
    | n + 1, .block ss _ => ss.flatMap (writes n)
    | n + 1, .if_ c a b _ => writesExpr n c ++ writes n a ++ writes n b
    | n + 1, .while_ c b _ => writesExpr n c ++ writes n b
    | n + 1, .for_ i c u b _ => writes n i ++ writesExpr n c ++ writes n u ++ writes n b
    | n + 1, .forOf _ _ c b _ => writesExpr n c ++ writes n b
    | n + 1, .measured _ b _ => writes n b
    | n + 1, .switch_ c cs _ => writesExpr n c ++ cs.flatMap (fun p => p.2.flatMap (writes n))
    | n + 1, .let_ _ _ _ e _ | n + 1, .expr e _ | n + 1, .return_ e _ => writesExpr n e
    | _, _ => []
end

def invalidate (ctx : Context) (names : List String) : Context :=
  { ctx with bindings := ctx.bindings.map fun b =>
    if names.contains b.name then { b with ty := b.declared.getD b.ty } else b }

def narrowBinding (ctx : Context) (name : String) (test : Ty → Bool) : Context :=
  { ctx with bindings := ctx.bindings.map fun b =>
    if b.name == name then { b with ty := (filterType test b.ty).getD b.ty, declared := some (b.declared.getD b.ty) } else b }

def narrow (ctx : Context) (condition : Expr) (truth : Bool) : Context :=
  match condition with
  | .unary "!" e _ => narrow ctx e (!truth)
  | .binary "&&" a b _ => if truth then narrow (narrow ctx a true) b true else ctx
  | .binary "||" a b _ => if !truth then narrow (narrow ctx a false) b false else ctx
  | .binary op (.var name _) (.literal lit _) _ =>
    let equal := truth == (op == "===" || op == "==")
    if ["===", "!==", "==", "!="].contains op then
      narrowBinding ctx name fun ty =>
        let matched :=  match lit, unreadonly ty with
          | .undefined, .undefined | .null, .null => true
          | .null, .undefined => op == "==" || op == "!="
          | .string a, .stringLiteral b => a == b
          | _, _ => false
        matched == equal
    else ctx
  | .binary op (.member (.var name _) field _) (.literal (.string units) _) _ =>
    if op == "===" || op == "!==" then
      narrowBinding ctx name fun ty =>
        let matched :=  match unreadonly ty with
          | .record fs => unreadonly ((fs.lookup field).getD .undefined) == .stringLiteral units
          | _ => false
        matched == (truth == (op == "==="))
    else ctx
  | _ => ctx

def protect (ctx : Context) (receiver : Expr) : Context :=
  { ctx with protectedRoots := receiverRoot ++ ctx.protectedRoots, inCallback := true }
where receiverRoot := (root receiver).toList

def checkWrite (ctx : Context) (target : Expr) (rebinding : Bool := false) : Checked Unit := do
  if let some name := root target then
    let b ← binding ctx name target.span
    if b.readOnly then error "A3001" "cannot mutate through a shared container read" target.span
    if !rebinding && immutable b.ty && referenceType b.ty then error "A3001" "cannot mutate an immutable value" target.span
    if !rebinding then
      match b.ty with
      | .readonly _ => error "A3001" "cannot mutate a readonly collection" target.span
      | _ => pure ()
    if ctx.protectedRoots.contains name then
      let b ← binding ctx name target.span
      throw {
        code := "A3002"
        message := s!"cannot mutate '{name}' while a traversal is reading it"
        span := target.span
        labels := [{ span := b.span, message := "collection declared here" }]
        help := some "Move the mutation outside the traversal, or use a separate owned collection."
      }

def literalType : Literal → Ty
  | .number _ _ => .number | .bigint _ => .bigint | .boolean _ => .boolean
  | .string s => .stringLiteral s | .null => .null | .undefined => .undefined

def reserved (name : String) : Bool :=
  ["#templateString", "NaN", "Infinity", "Math", "Number", "BigInt", "Map", "Set", "Array", "Object", "Reflect",
    "eval", "Function", "globalThis", "__proto__", "constructor", "prototype"].contains name

def join (a b : Ty) : Ty := if a == b then a else .union a b


mutual
  def infer (fuel : Nat) (ctx : Context) (expr : Expr) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" expr.span
    | n + 1 =>
      match expr with
      | .literal value _ => return literalType value
      | .var name span =>
        if name == "NaN" || name == "Infinity" then return .number
        return (← binding ctx name span).ty
      | .unary op e span =>
        let t ← infer n ctx e
        if op == "!" then
          requireType t .boolean span
          return .boolean
        if t == .number || (op == "-" && t == .bigint) then return t
        error "A2002" s!"invalid operand {typeName t} for '{op}'" span
      | .binary op a b span =>
        let ta ← infer n ctx a
        if op == "??" then
          if !(compatible .undefined ta || compatible .null ta) then
            error "A2002" "left operand of '??' must be an optional value" span
          let some t := filterType (fun t => t != .undefined && t != .null) ta
            | error "A2002" "nullish operand needs a value type" span
          checkExpr n ctx b t
          return t
        let tb ← infer n (if op == "&&" then narrow ctx a true else if op == "||" then narrow ctx a false else ctx) b
        if op == "==" || op == "!=" then return .boolean
        if op == "===" || op == "!==" then
          if (referenceType ta || referenceType tb) && ta != .undefined && tb != .undefined && ta != .null && tb != .null then
            error "A1001" "reference identity comparison is not supported" span
          if !(compatible ta tb || compatible tb ta || (match ta, tb with | .stringLiteral _, .stringLiteral _ => true | _, _ => false)) then
            error "A2002" "comparison operands have incompatible types" span
          return .boolean
        let ta := match unreadonly ta with | .stringLiteral _ => Ty.string | t => t
        let tb := match unreadonly tb with | .stringLiteral _ => Ty.string | t => t
        requireType tb ta b.span
        if op == "&&" || op == "||" then requireType ta .boolean a.span; return .boolean
        if ["<", "<=", ">", ">="].contains op then
          if ![Ty.number, .bigint, .string].contains ta then
            error "A2002" "ordered comparison requires numeric or string operands" span
          return .boolean
        if ta == .number || ta == .bigint || (op == "+" && ta == .string) then return ta
        error "A2002" s!"operator '{op}' does not accept {typeName ta}" span
      | .conditional c a b _ =>
        requireType (← infer n ctx c) .boolean c.span
        return join (← infer n (narrow ctx c true) a) (← infer n (narrow ctx c false) b)
      | .array xs span =>
        if xs.isEmpty then error "A2004" "empty arrays need a type annotation" span
        let ts ← xs.mapM fun x => match x with
          | .spread e _ => do
            match unreadonly (← infer n ctx e) with
            | .array t | .iterator t | .set t => return t
            | .map k v => return .tuple [k, v]
            | _ => error "A2002" "array spread requires an array" e.span
          | _ => infer n ctx x
        let t := ts.foldl join ts.head!
        for (x, tx) in xs.zip ts do
          requireType tx t x.span
          if referenceType tx && !immutable tx && !fresh x then
            error "A3001" "stored mutable references must be freshly allocated" x.span
        return .array t
      | .record fields _ =>
        let mut ts : List (String × Ty) := []
        for (key, value) in fields do
          if key == "" then
            let .record fs := unreadonly (← infer n ctx value)
              | error "A2002" "object spread requires a record" value.span
            if fs.any (fun (_, t) => referenceType t && !immutable t) then
              error "A3001" "object spread would share mutable fields" value.span
            for (k, t) in fs do ts := (ts.filter (·.1 != k)) ++ [(k, t)]
          else
            if reserved key then error "A3004" s!"reserved property '{key}'" value.span
            let t ← infer n ctx value
            if referenceType t && !immutable t && !fresh value then
              error "A3001" "stored mutable references must be freshly allocated" value.span
            ts := (ts.filter (·.1 != key)) ++ [(key, t)]
        return .record ts
      | .newMap key value span =>
        let k ← resolve 100 ctx.program key
        let v ← resolve 100 ctx.program value
        if referenceType k then error "A3001" "Map keys must be scalar" span
        requireSupportedType v span
        return .map k v
      | .newSet element span =>
        let t ← resolve 100 ctx.program element
        if referenceType t then error "A3001" "Set elements must be scalar" span
        return .set t
      | .newClass name args span =>
        let some c := ctx.program.classes.find? (·.name == name)
          | error "A2001" s!"unknown class '{name}'" span
        let params := c.constructor_.map Function.params |>.getD []
        if args.length != params.length then error "A2007" "constructor argument count mismatch" span
        let mut roots : List String := []
        for (arg, param) in args.zip params do
          let ty ← resolve 100 ctx.program param.ty
          checkExpr n ctx arg ty
          if referenceType ty then
            if immutable ty && !fresh arg then
              if !immutable (← infer n ctx arg) then error "A3001" "a mutable owner cannot be shared with a constructor" arg.span
            if !immutable ty then checkWrite ctx arg
            if let some r := root arg then
              if roots.contains r then error "A3001" "overlapping constructor arguments" arg.span
              roots := r :: roots
        return .class_ name
      | .spread _ span => error "A1001" "spread is allowed only inside array/object literals" span
      | .member object field span =>
        if reserved field then error "A3004" s!"access to '{field}' is forbidden by the runtime contract" span
        let t := unreadonly (← infer n ctx object)
        match t, field with
        | .array _, "length" | .tuple _, "length" | .string, "length" | .stringLiteral _, "length" | .map _ _, "size" | .set _, "size" => return .number
        | .record fs, _ =>
          let some ty := fs.lookup field | error "A2006" s!"record has no field '{field}'" span
          return match ty with | .fieldReadonly t => t | t => t
        | .class_ name, _ =>
          let some c := ctx.program.classes.find? (·.name == name) | error "A2001" "unknown class" span
          let some f := c.fields.find? (·.name == field) | error "A2006" s!"unknown field '{field}'" span
          if f.private_ && ctx.currentClass != some name then error "A3004" "private field access" span
          match f.ty with
          | some ty => resolve 100 ctx.program ty
          | none => infer n { ctx with bindings := [] } f.value
        | .union a b, _ =>
          let lookup := fun t => match unreadonly t with
            | .record fs => (fs.lookup field).map unreadonly
            | _ => none
          match lookup a, lookup b with
          | some a, some b => return join a b
          | _, _ => error "A2006" "narrow the union before accessing this field" span
        | _, _ => error "A2006" s!"unknown property '{field}' on {typeName t}" span
      | .index object index span =>
        requireType (← infer n ctx index) .number index.span
        match unreadonly (← infer n ctx object) with
        | .array t => return .union t .undefined
        | .string | .stringLiteral _ => return .union .string .undefined
        | .tuple ts =>
          match index with
          | .literal (.number i 0) _ =>
            let some t := ts[i]? | error "A2002" "tuple index is out of bounds" span
            return t
          | _ => error "A1001" "tuple indices must be integer literals" span
        | _ => error "A2002" "indexing requires an array, tuple, or string" span
      | .lambda params body span =>
        let params ← params.mapM fun p => return { p with ty := ← resolve 100 ctx.program p.ty }
        if (params.map Param.name).eraseDups.length != params.length then
          error "A2005" "duplicate callback parameter" span
        for param in params do
          if reserved param.name || ctx.program.functions.any (fun f => f.name == param.name) then
            error "A3004" s!"cannot shadow reserved name '{param.name}'" param.span
          if ctx.bindings.any (fun b => b.name == param.name) then
            error "A2005" "callback parameter shadowing is not supported" param.span
        let bindings := params.map fun p => ({ name := p.name, ty := p.ty, mutable := true, borrowed := referenceType p.ty, readOnly := referenceType p.ty, span := p.span } : Binding)
        let inner := { ctx with bindings := bindings ++ ctx.bindings, result := .void, loopDepth := 0, switchDepth := 0, inCallback := true, protectedRoots := (if ctx.pureCallback then ctx.bindings.map Binding.name else []) ++ ctx.protectedRoots }
        let result ← inferCallback n inner body
        let _ ← checkStmt n { inner with result, inferReturns := false } body
        if referenceType result then error "A3001" "callbacks cannot return mutable references" span
        return .function (params.map Param.ty) result
      | .call callee args span =>
        match callee with
        | .var name _ =>
          if name == "#templateString" then
            match args with
            | [arg] =>
              let t := unreadonly (← infer n ctx arg)
              if !scalarPrintable t then error "A1001" "template interpolation requires scalar values" span
              return .string
            | _ => error "A2007" "invalid template interpolation" span
          if ["Number", "BigInt"].contains name then
            if args.length != 1 then error "A2007" "conversion requires exactly one argument" span
            let t ← infer n ctx args.head!
            if t != .number && t != .bigint then error "A2002" "conversion accepts number or bigint" span
            return if name == "Number" then .number else .bigint
          if ctx.inCallback then error "A3003" "user function calls inside callbacks require interprocedural effect summaries" span
          let some f := ctx.program.functions.find? (fun f => f.name == name)
            | error "A2003" s!"unknown function '{name}'" span
          if args.length != f.params.length then error "A2007" s!"'{name}' expects {f.params.length} arguments" span
          let mut roots : List String := []
          for (arg, param) in args.zip f.params do
            let expected ← resolve 100 ctx.program param.ty
            checkExpr n ctx arg expected
            if referenceType expected then
              if immutable expected && !fresh arg then
                if !immutable (← infer n ctx arg) then
                  error "A3001" "a mutable owner cannot be shared as an immutable argument" arg.span
              if let some r := root arg then
                if !immutable expected then checkWrite ctx arg
                if roots.contains r then error "A3001" s!"'{r}' is passed through overlapping mutable arguments" arg.span
                roots := r :: roots
          resolve 100 ctx.program f.result
        | .member object field _ => inferMethod n ctx object field args span
        | _ => error "A1001" "only named functions and supported collection methods may be called" span

  /-- Infer a callback's final return after checking its local declarations.
  Earlier value-returning exits require an explicit named function instead. -/
  def inferCallback (fuel : Nat) (ctx : Context) (body : Stmt) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "callback inference resource bound exceeded" body.span
    | n + 1 =>
      match body with
      | .return_ e _ => infer n ctx e
      | .block stmts _ => inferCallbackBlock n ctx stmts
      | .if_ condition yes no _ =>
        checkExpr n ctx condition .boolean
        return join (← inferCallback n ctx yes) (← inferCallback n ctx no)
      | _ => let _ ← checkStmt n ctx body; return .void

  def inferCallbackBlock (fuel : Nat) (ctx : Context) (stmts : List Stmt) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "callback inference resource bound exceeded" {}
    | n + 1 =>
      match stmts with
      | [] => return .void
      | [last] => inferCallback n ctx last
      | first :: rest => inferCallbackBlock n (← checkStmt n { ctx with inferReturns := true } first) rest

  def checkExpr (fuel : Nat) (ctx : Context) (expr : Expr) (expected : Ty) : Checked Unit := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" expr.span
    | n + 1 =>
      match expr, unreadonly expected with
      | .array xs _, .array t =>
        for x in xs do
          match x with
          | .spread e _ =>
            let item ← match unreadonly (← infer n ctx e) with
              | .array t | .iterator t | .set t => pure t
              | .map k v => pure (.tuple [k, v])
              | _ => error "A2002" "spread requires a collection or iterator" e.span
            requireType item t e.span
            if referenceType item && !immutable item then error "A3001" "spread would share mutable elements" e.span
          | _ =>
            checkExpr n ctx x t
            if referenceType t && !immutable t && !fresh x then
              error "A3001" "stored mutable references must be freshly allocated" x.span
      | .array xs span, .tuple ts =>
        if xs.length != ts.length then error "A2002" "tuple length does not match its annotation" span
        for (x, t) in xs.zip ts do
          checkExpr n ctx x t
          if referenceType t && !immutable t && !fresh x then error "A3001" "tuple members must be immutable or fresh" x.span
      | _, _ => requireType (← infer n ctx expr) expected expr.span

  def inferMethod (fuel : Nat) (ctx : Context) (object : Expr) (name : String)
      (args : List Expr) (span : Span) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" span
    | n + 1 =>
      if let .var namespace_ _ := object then
        if namespace_ == "Math" || namespace_ == "Number" then
          if namespace_ == "Math" && ["min", "max"].contains name then
            for arg in args do checkExpr n ctx arg .number
            return .number
          if args.length != 1 then error "A2007" "numeric builtin requires one argument" span
          let t ← infer n ctx args.head!
          if namespace_ == "Number" && ["isNaN", "isFinite"].contains name then return .boolean
          if namespace_ == "Math" && ["abs", "floor", "trunc", "sqrt"].contains name then
            requireType t .number span
            return .number
          error "A1001" s!"builtin '{namespace_}.{name}' is not supported" span
      let raw ← infer n ctx object
      let ty := match unreadonly raw with | .stringLiteral _ => Ty.string | t => t
      if ["push", "pop", "set", "add", "delete", "clear"].contains name then
        checkWrite ctx object
        if sharedRead object || ((root object).isNone && !fresh object) then
          error "A3001" "only an owner may mutate a collection" span
        if let .readonly _ := raw then error "A3001" "cannot mutate a readonly collection" span
      if let .class_ className := ty then
        if ctx.inCallback then error "A3003" "class method calls require effect summaries in callbacks" span
        checkWrite ctx object
        let some c := ctx.program.classes.find? (·.name == className) | error "A2001" "unknown class" span
        let some method := c.methods.find? (·.name == name) | error "A2006" "unknown method" span
        if args.length != method.params.length then error "A2007" "method argument count mismatch" span
        for (arg, param) in args.zip method.params do
          let expected ← resolve 100 ctx.program param.ty
          checkExpr n ctx arg expected
          if referenceType expected then error "A3001" "reference method arguments require effect summaries" arg.span
        resolve 100 ctx.program method.result
      else
        inferCollectionMethod n ctx object ty name args span

  def inferCollectionMethod (fuel : Nat) (ctx : Context) (object : Expr) (ty : Ty) (name : String)
      (args : List Expr) (span : Span) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" span
    | n + 1 =>
      match ty, name, args with
      | .array t, "push", [arg] =>
        checkExpr n ctx arg t
        if referenceType t && !immutable t && !fresh arg then error "A3001" "stored mutable references must be fresh" arg.span
        return .number
      | .array t, "pop", [] => return .union t .undefined
      | .array t, "slice", [] | .array t, "toReversed", [] =>
        if referenceType t && !immutable t then error "A3001" "copy would share mutable elements" span
        return .array t
      | .array t, "slice", [a] =>
        checkExpr n ctx a .number
        if referenceType t && !immutable t then error "A3001" "copy would share mutable elements" span
        return .array t
      | .array t, "slice", [a, b] =>
        checkExpr n ctx a .number; checkExpr n ctx b .number
        if referenceType t && !immutable t then error "A3001" "copy would share mutable elements" span
        return .array t
      | .array t, "map", [fn] | .array t, "filter", [fn] | .array t, "forEach", [fn] =>
        let ft ← infer n { (protect ctx object) with pureCallback := name != "forEach" } fn
        let .function ps r := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [] && ps != [t] && ps != [t, .number] then error "A2002" "callback parameters do not match array element/index types" fn.span
        if name == "filter" then
          if referenceType t && !immutable t then error "A3001" "filter would share mutable elements" span
          requireType r .boolean fn.span
          return .array t
        return if name == "map" then .array r else .void
      | .array t, "reduce", [fn, initial] =>
        let acc ← infer n ctx initial
        let ft ← infer n { (protect ctx object) with pureCallback := name != "forEach" } fn
        let .function ps r := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [] && ps != [acc] && ps != [acc, t] && ps != [acc, t, .number] then error "A2002" "reduce callback parameters do not match" fn.span
        requireType r acc fn.span
        return acc
      | .array t, "some", [fn] | .array t, "every", [fn] |
          .array t, "find", [fn] | .array t, "findIndex", [fn] =>
        let ft ← infer n { (protect ctx object) with pureCallback := true } fn
        let .function ps r := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [] && ps != [t] && ps != [t, .number] then error "A2002" "callback parameters do not match array element/index types" fn.span
        requireType r .boolean fn.span
        return if name == "find" then .union t .undefined
          else if name == "findIndex" then .number else .boolean
      | .array t, "toSorted", [fn] =>
        if referenceType t && !immutable t then error "A3001" "sorting would share mutable elements" span
        let ft ← infer n { (protect ctx object) with pureCallback := true } fn
        let .function ps r := ft | error "A2002" "expected a typed comparator" fn.span
        if ps != [] && ps != [t] && ps != [t, t] then error "A2002" "comparator parameters must be array elements" fn.span
        requireType r .number fn.span
        return .array t
      | .array t, "concat", args =>
        if referenceType t && !immutable t then error "A3001" "concatenation would share mutable elements" span
        for arg in args do
          match unreadonly (← infer n ctx arg) with
          | .array a => requireType a t arg.span
          | a => requireType a t arg.span
        return .array t
      | .array t, "join", [] | .array t, "join", [_] =>
        if !scalarPrintable t then error "A1001" "join requires scalar array elements" span
        for arg in args do checkExpr n ctx arg .string
        return .string
      | .map k v, "get", [key] => checkExpr n ctx key k; return .union v .undefined
      | .map k _, "has", [key] | .map k _, "delete", [key] => checkExpr n ctx key k; return .boolean
      | .map k v, "set", [key, value] =>
        checkExpr n ctx key k; checkExpr n ctx value v
        if referenceType v && !immutable v && !fresh value then error "A3001" "stored mutable references must be fresh" value.span
        return ty
      | .map _ _, "clear", [] => return .void
      | .map k v, "forEach", [fn] =>
        let ft ← infer n { (protect ctx object) with pureCallback := name != "forEach" } fn
        let .function ps _ := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [] && ps != [v, k] && ps != [v] then error "A2002" "Map callback takes value, then key" fn.span
        return .void
      | .set t, "add", [v] | .set t, "has", [v] | .set t, "delete", [v] =>
        checkExpr n ctx v t
        return if name == "add" then ty else .boolean
      | .set _, "clear", [] => return .void
      | .map k _, "keys", [] => return .iterator k
      | .map _ v, "values", [] =>
        if referenceType v && !immutable v then error "A3001" "values would share mutable elements" span
        return .iterator v
      | .map k v, "entries", [] =>
        if referenceType v && !immutable v then error "A3001" "entries would share mutable elements" span
        return .iterator (.tuple [k, v])
      | .set t, "keys", [] | .set t, "values", [] => return .iterator t
      | .set t, "entries", [] => return .iterator (.tuple [t, t])
      | .array t, "includes", [v] | .array t, "indexOf", [v] |
          .array t, "includes", [v, _] | .array t, "indexOf", [v, _] =>
        if referenceType t then error "A1001" "reference identity search is unsupported" span
        checkExpr n ctx v t
        if let some start := args[1]? then checkExpr n ctx start .number
        return if name == "includes" then .boolean else .number
      | .array t, "entries", [] =>
        if referenceType t && !immutable t then error "A3001" "entries would share mutable elements" span
        return .iterator (.tuple [.number, t])
      | .string, "charCodeAt", [i] => checkExpr n ctx i .number; return .number
      | .string, "charCodeAt", [] => return .number
      | .string, "slice", [] => return .string
      | .string, "slice", [a] => checkExpr n ctx a .number; return .string
      | .string, "slice", [a, b] => checkExpr n ctx a .number; checkExpr n ctx b .number; return .string
      | .string, "startsWith", [a] | .string, "endsWith", [a] |
          .string, "includes", [a] | .string, "indexOf", [a] |
          .string, "startsWith", [a, _] | .string, "endsWith", [a, _] |
          .string, "includes", [a, _] | .string, "indexOf", [a, _] =>
        checkExpr n ctx a .string
        if let some pos := args[1]? then checkExpr n ctx pos .number
        return if name == "indexOf" then .number else .boolean
      | _, _, _ => error "A1001" s!"unsupported method or argument list: {typeName ty}.{name}" span

  def checkStmt (fuel : Nat) (ctx : Context) (stmt : Stmt) : Checked Context := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" stmt.span
    | n + 1 =>
      match stmt with
      | .block stmts _ =>
        let _ ← checkBlock n ctx stmts
        return invalidate ctx (writes n stmt)
      | .let_ mutable name annotation value span =>
        if reserved name || ctx.program.functions.any (fun f => f.name == name) then error "A3004" s!"cannot shadow reserved intrinsic '{name}'" span
        if ctx.bindings.any (fun b => b.name == name) then error "A2005" s!"shadowing or duplicate declaration of '{name}' is not supported" span
        let t ← match annotation with
          | some ty =>
            let ty ← resolve 100 ctx.program ty
            requireSupportedType ty span
            checkExpr n ctx value ty
            pure ty
          | none => do
            let ty ← infer n ctx value
            pure (match ty with | .stringLiteral _ => Ty.string | t => t)
        if let .iterator _ := t then error "A3001" "consume an iterator immediately with spread or for-of" value.span
        let borrowed := referenceType t && sharedRead value
        if referenceType t && !immutable t && !fresh value && !borrowed then
          error "A3001" "reference bindings require a fresh allocation or an owned function result" value.span
        if immutable t && referenceType t && !fresh value then
          if !immutable (← infer n ctx value) then
            error "A3001" "a readonly alias cannot share a mutable owner" value.span
        return { ctx with bindings := { name, ty := t, mutable, borrowed, readOnly := borrowed, span } :: ctx.bindings }
      | .assign target value span =>
        checkWrite ctx target (match target with | .var .. => true | _ => false)
        match target with
        | .var name _ =>
          let b ← binding ctx name target.span
          if !b.mutable then error "A2008" s!"cannot assign to const binding '{name}'" span
          let ty := b.declared.getD b.ty
          if referenceType ty && !immutable ty && !fresh value then error "A3001" "reassigning owned references requires a fresh value" span
          checkExpr n ctx value ty
        | .index object index _ =>
          checkExpr n ctx index .number
          let .array t ← infer n ctx object | error "A2002" "indexed assignment requires an array" span
          checkExpr n ctx value t
          if referenceType t && !immutable t && !fresh value then error "A3001" "stored mutable elements must be fresh" span
        | .member object field _ =>
          match unreadonly (← infer n ctx object) with
          | .record fields =>
            let some t := fields.lookup field | error "A2006" s!"unknown field '{field}'" span
            if let .fieldReadonly _ := t then error "A3001" "cannot assign a readonly field" span
            checkExpr n ctx value t
            if referenceType t && !immutable t && !fresh value then error "A3001" "stored mutable fields must be fresh" span
          | .class_ name =>
            let some c := ctx.program.classes.find? (·.name == name) | error "A2001" "unknown class" span
            let some f := c.fields.find? (·.name == field) | error "A2006" "unknown field" span
            if f.private_ && ctx.currentClass != some name then error "A3004" "private field access" span
            if f.readonly_ then error "A3001" "cannot assign a readonly field" span
            let ty ← infer n ctx target
            checkExpr n ctx value ty
            if referenceType ty && !immutable ty && !fresh value then error "A3001" "stored mutable fields must be fresh" span
          | _ => error "A3004" "only declared fields may be assigned" span
        | _ => error "A2002" "invalid assignment target" span
        return invalidate ctx (writes n stmt)
      | .expr e _ => let _ ← infer n ctx e; return invalidate ctx (writesExpr n e)
      | .if_ c yes no _ =>
        checkExpr n ctx c .boolean
        let _ ← checkStmt n (narrow ctx c true) yes
        let _ ← checkStmt n (narrow ctx c false) no
        let out := if exits n yes then narrow ctx c false else if exits n no then narrow ctx c true else ctx
        return invalidate out (writes n stmt)
      | .while_ c body _ =>
        let ctx := invalidate ctx (writes n body)
        checkExpr n ctx c .boolean
        let _ ← checkStmt n { (narrow ctx c true) with loopDepth := ctx.loopDepth + 1 } body
        return ctx
      | .for_ init c update body _ =>
        let inner ← checkStmt n ctx init
        let inner := invalidate inner (writes n body ++ writes n update)
        checkExpr n inner c .boolean
        let _ ← checkStmt n inner update
        let _ ← checkStmt n { inner with loopDepth := inner.loopDepth + 1 } body
        return ctx
      | .measured measure body _ =>
        let ty ← infer n { ctx with inCallback := true, pureCallback := true } measure
        if ty != .number && ty != .bigint then error "A2002" "a measure must have a numeric type" measure.span
        checkStmt n ctx body
      | .forOf mutable name collection body span =>
        if reserved name || ctx.bindings.any (·.name == name) then error "A2005" "duplicate or reserved loop binding" span
        let ty := unreadonly (← infer n ctx collection)
        let t ← match ty with
          | .array t | .set t | .iterator t => pure t
          | .map k v => pure (.tuple [k, v])
          | _ => error "A2002" "for-of requires an array, Map, or Set" span
        let ctx := invalidate ctx (writes n body)
        let inner := { ctx with loopDepth := ctx.loopDepth + 1, protectedRoots := (root collection).toList ++ ctx.protectedRoots, bindings := { name, ty := t, mutable, borrowed := referenceType t, readOnly := referenceType t, span } :: ctx.bindings }
        let _ ← checkStmt n inner body
        return ctx
      | .switch_ value cases span =>
        let _ ← infer n ctx value
        if (cases.filter (·.1.isNone)).length > 1 then error "A2005" "duplicate default clause" span
        for (label, body) in cases do
          let inner := { ctx with switchDepth := ctx.switchDepth + 1 }
          let inner ← match label with
            | none => pure inner
            | some label =>
              match label with
              | .literal .. => pure ()
              | _ => error "A1001" "switch cases require literal labels" label.span
              let _ ← infer n ctx (.binary "===" value label span)
              pure (narrow inner (.binary "===" value label span) true)
          if !exits n (.block body span) then
            error "A1001" "nonempty switch clauses must end in break, continue, or return" span
          let _ ← checkBlock n inner body
        return ctx
      | .return_ e span =>
        if ctx.inferReturns then
          let _ ← infer n ctx e
          return ctx
        checkExpr n ctx e ctx.result
        if referenceType ctx.result && root e == some "this" then
          error "A3001" "this and its mutable fields cannot escape a method" span
        if referenceType ctx.result && !immutable ctx.result then
          match e with
          | .var name _ =>
            let b ← binding ctx name span
            if b.borrowed then error "A3001" "returning a borrowed reference would escape its lifetime" span
          | .array .. | .record .. | .newMap .. | .newSet .. | .newClass .. => pure ()
          | .call (.var ..) _ _ => pure ()
          | .call (.member _ method _) _ _ =>
            if !["map", "filter", "slice", "concat", "toReversed", "toSorted", "keys", "values", "entries"].contains method then
              error "A3001" "a returned reference must be owned; this method can return its receiver" span
          | _ => error "A3001" "return an owned local variable or a fresh collection" span
        return ctx
      | .break_ span =>
        if ctx.loopDepth == 0 && ctx.switchDepth == 0 then error "A2009" "break is only valid inside a loop or switch" span
        return ctx
      | .continue_ span =>
        if ctx.loopDepth == 0 then error "A2009" "continue is only valid inside a loop" span
        return ctx

  def checkBlock (fuel : Nat) (ctx : Context) (stmts : List Stmt) : Checked Context := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" {}
    | n + 1 =>
      match stmts with
      | [] => return ctx
      | stmt :: rest => checkBlock n (← checkStmt n ctx stmt) rest
end

def returns (fuel : Nat) (stmt : Stmt) : Bool :=
  let out := flow fuel stmt
  out.returned && !(out.normal || out.broken || out.continued)

def program (p : Program) : Checked Unit := do
  if (p.functions.map Function.name).eraseDups.length != p.functions.length then
    error "A2005" "duplicate function declaration" {}
  if (p.aliases.map Prod.fst).eraseDups.length != p.aliases.length then
    error "A2005" "duplicate type alias" {}
  for (name, ty) in p.aliases do
    if reserved name || ["number", "bigint", "string", "boolean", "undefined", "null", "void"].contains name then
      error "A3004" s!"cannot shadow builtin type '{name}'" {}
    requireSupportedType (← resolve 100 p ty) {}
  for f in p.functions do
    if reserved f.name then error "A3004" s!"cannot shadow intrinsic '{f.name}'" f.span
    if (f.params.map Param.name).eraseDups.length != f.params.length then
      error "A2005" "duplicate parameter" f.span
    let bindings ← f.params.mapM fun param => do
      if reserved param.name || p.functions.any (fun f => f.name == param.name) then error "A3004" s!"cannot shadow intrinsic '{param.name}'" param.span
      let t ← resolve 100 p param.ty
      requireSupportedType t param.span
      return { name := param.name, ty := t, mutable := true, borrowed := referenceType t, span := param.span : Binding }
    let result ← resolve 100 p f.result
    requireSupportedType result f.span
    if let some measure := f.decreases then
      let ty ← infer 256 { program := p, bindings, result, inCallback := true } measure
      if ty != .number && ty != .bigint then error "A2002" "a measure must have a numeric type" measure.span
    let _ ← checkStmt 256 { program := p, bindings, result } f.body
    if result != .void && !returns 256 f.body then
      error "A2010" s!"function '{f.name}' may fall through without returning a value" f.span
  if (p.classes.map Class.name).eraseDups.length != p.classes.length then
    error "A2005" "duplicate class declaration" {}
  for c in p.classes do
    if reserved c.name || p.aliases.any (·.1 == c.name) || p.functions.any (·.name == c.name) then
      error "A3004" "duplicate or reserved class name" c.span
    let names := c.fields.map Field.name ++ c.methods.map Function.name
    if names.eraseDups.length != names.length then error "A2005" "duplicate class member" c.span
    for field in c.fields do
      if reserved field.name then error "A3004" "reserved class field" field.span
      let ctx : Context := { program := p }
      let ty ← match field.ty with
        | some ty =>
          let ty ← resolve 100 p ty
          checkExpr 256 ctx field.value ty
          pure ty
        | none => infer 256 ctx field.value
      requireSupportedType ty field.span
      if referenceType ty && !immutable ty && !fresh field.value then
        error "A3001" "field initializer must be fresh" field.span
    for method in c.constructor_.toList ++ c.methods do
      let bindings ← method.params.mapM fun param => do
        let ty ← resolve 100 p param.ty
        requireSupportedType ty param.span
        return { name := param.name, ty, mutable := true, borrowed := referenceType ty, span := param.span : Binding }
      if (bindings.map Binding.name).eraseDups.length != bindings.length || bindings.any (fun b => reserved b.name || b.name == "this") then
        error "A2005" "duplicate or reserved method parameter" method.span
      let result ← resolve 100 p method.result
      let ctx : Context := { program := p, result, currentClass := some c.name, bindings := { name := "this", ty := .class_ c.name, mutable := false, borrowed := true } :: bindings }
      let _ ← checkStmt 256 ctx method.body
      if result != .void && !returns 256 method.body then
        error "A2010" "method may fall through without returning" method.span

end Check

def frontend (source : String) : Checked Program := do
  let program ← parse source
  Check.program program
  return program

end Ariadne

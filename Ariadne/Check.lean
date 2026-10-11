import Ariadne.Parser

namespace Ariadne
namespace Check

structure Binding where
  name : String
  ty : Ty
  mutable : Bool
  borrowed : Bool := false
  span : Span := {}
  deriving Repr

structure Context where
  program : Program
  bindings : List Binding := []
  result : Ty := .void
  loopDepth : Nat := 0
  /-- Collection roots protected while a callback runs. -/
  protectedRoots : List String := []
  /-- Callbacks may not call user functions until interprocedural effects are available. -/
  inCallback : Bool := false

def error (code message : String) (span : Span) (help : Option String := none) : Checked α :=
  .error { code, message, span, help }

def resolve (fuel : Nat) (p : Program) (ty : Ty) : Checked Ty := do
  match fuel with
  | 0 => error "A2001" "cyclic or excessively nested type alias" {}
  | n + 1 =>
    match ty with
    | .named name =>
      let some t := p.aliases.lookup name | error "A2001" s!"unknown type '{name}'" {}
      resolve n p t
    | .array t => return .array (← resolve n p t)
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
  | .map k v => s!"Map<{typeName k}, {typeName v}>"
  | .union a b => s!"{typeName a} | {typeName b}"
  | .tuple _ => "tuple" | .record _ => "record" | .function _ _ => "callback"
  | .named n => n

def referenceType : Ty → Bool
  | .array _ | .map _ _ | .record _ | .tuple _ | .function _ _ => true
  | .union a b => referenceType a || referenceType b
  | _ => false

def compatible (actual expected : Ty) : Bool :=
  actual == expected || match expected with
    | .union a b => compatible actual a || compatible actual b
    | .void => actual == .undefined
    | _ => false
termination_by sizeOf expected

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
  | _ => none

def protect (ctx : Context) (receiver : Expr) : Context :=
  { ctx with protectedRoots := receiverRoot ++ ctx.protectedRoots, inCallback := true }
where receiverRoot := (root receiver).toList

def checkWrite (ctx : Context) (target : Expr) : Checked Unit := do
  if let some name := root target then
    if ctx.protectedRoots.contains name then
      let b ← binding ctx name target.span
      throw { code := "A3002", message := s!"cannot mutate '{name}' while a traversal is reading it", span := target.span, labels := [{ span := b.span, message := "collection declared here" }], help := some "Move the mutation outside the traversal, or use a separate owned collection." }

def literalType : Literal → Ty
  | .number _ _ => .number | .bigint _ => .bigint | .boolean _ => .boolean
  | .string _ => .string | .null => .null | .undefined => .undefined

def reserved (name : String) : Bool :=
  ["NaN", "Infinity", "Math", "Number", "BigInt", "Map", "Array", "Object", "Reflect", "eval", "Function", "globalThis", "__proto__", "constructor", "prototype"].contains name

def join (a b : Ty) : Ty := if a == b then a else .union a b

def callbackResult : Nat → Stmt → Option Expr
  | 0, _ => none
  | _ + 1, .return_ e _ => some e
  | n + 1, .block stmts _ => stmts.getLast?.bind (callbackResult n)
  | _, _ => none

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
        let tb ← infer n ctx b
        if op == "??" then
          match ta with
          | .union t .undefined | .union t .null => requireType tb t span; return t
          | _ => error "A2002" "left operand of '??' must be an optional value" span
        if op == "===" || op == "!==" then
          if referenceType ta || referenceType tb then
            error "A1001" "reference identity comparison is not supported" span
          if !(compatible ta tb || compatible tb ta) then
            error "A2002" "comparison operands have incompatible types" span
          return .boolean
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
        return join (← infer n ctx a) (← infer n ctx b)
      | .array xs span =>
        if xs.isEmpty then error "A2004" "empty arrays need a type annotation" span
        let ts ← xs.mapM (infer n ctx)
        let t := ts.head!
        for (x, tx) in xs.zip ts do
          requireType tx t x.span
          if referenceType tx then error "A3001" "nested mutable references require ownership transfer support" x.span
        return .array t
      | .record fields _ =>
        let ts ← fields.mapM fun (key, value) => do
          if reserved key then error "A3004" s!"reserved property '{key}'" value.span
          let t ← infer n ctx value
          if referenceType t then error "A3001" "record fields must initially contain scalar values" value.span
          return (key, t)
        if (fields.map Prod.fst).eraseDups.length != fields.length then
          error "A2005" "duplicate record field" expr.span
        return .record ts
      | .newMap key value span =>
        let k ← resolve 100 ctx.program key
        let v ← resolve 100 ctx.program value
        if referenceType k || referenceType v then error "A3001" "Map keys and values must initially be scalar" span
        return .map k v
      | .member object field span =>
        if reserved field then error "A3004" s!"access to '{field}' is forbidden by the runtime contract" span
        let t ← infer n ctx object
        match t, field with
        | .array _, "length" | .tuple _, "length" | .string, "length" | .map _ _, "size" => return .number
        | .record fs, _ =>
          let some ty := fs.lookup field | error "A2006" s!"record has no field '{field}'" span
          return ty
        | _, _ => error "A2006" s!"unknown property '{field}' on {typeName t}" span
      | .index object index span =>
        requireType (← infer n ctx index) .number index.span
        match ← infer n ctx object with
        | .array t => return .union t .undefined
        | .string => return .union .string .undefined
        | .tuple ts =>
          match index with
          | .literal (.number i 0) _ =>
            let some t := ts[i]? | error "A2002" "tuple index is out of bounds" span
            return t
          | _ => error "A1001" "tuple indices must be integer literals" span
        | _ => error "A2002" "indexing requires an array, tuple, or string" span
      | .lambda params body span =>
        let params ← params.mapM fun p => return { p with ty := ← resolve 100 ctx.program p.ty }
        let bindings := params.map fun p => ({ name := p.name, ty := p.ty, mutable := true, borrowed := referenceType p.ty, span := p.span } : Binding)
        let inner := { ctx with bindings := bindings ++ ctx.bindings, result := .void, loopDepth := 0, inCallback := true }
        let result ← match callbackResult n body with
          | some e =>
            -- Block-local return types are inferred by the checked statement traversal below.
            match infer n inner e with
            | .ok t => pure t
            | .error _ => pure Ty.void
          | none => pure Ty.void
        let _ ← checkStmt n { inner with result } body
        if referenceType result then error "A3001" "callbacks cannot return mutable references" span
        return .function (params.map Param.ty) result
      | .call callee args span =>
        match callee with
        | .var name _ =>
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
              if let some r := root arg then
                if roots.contains r then error "A3001" s!"'{r}' is passed through overlapping mutable arguments" arg.span
                roots := r :: roots
          resolve 100 ctx.program f.result
        | .member object field _ => inferMethod n ctx object field args span
        | _ => error "A1001" "only named functions and supported collection methods may be called" span

  def checkExpr (fuel : Nat) (ctx : Context) (expr : Expr) (expected : Ty) : Checked Unit := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" expr.span
    | n + 1 =>
      match expr, expected with
      | .array xs _, .array t =>
        for x in xs do
          checkExpr n ctx x t
          if referenceType t then error "A3001" "nested mutable references are not supported" x.span
      | .array xs span, .tuple ts =>
        if xs.length != ts.length then error "A2002" "tuple length does not match its annotation" span
        for (x, t) in xs.zip ts do checkExpr n ctx x t
      | _, _ => requireType (← infer n ctx expr) expected expr.span

  def inferMethod (fuel : Nat) (ctx : Context) (object : Expr) (name : String)
      (args : List Expr) (span : Span) : Checked Ty := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" span
    | n + 1 =>
      if let .var namespace_ _ := object then
        if namespace_ == "Math" || namespace_ == "Number" then
          if args.length != 1 then error "A2007" "numeric builtin requires one argument" span
          let t ← infer n ctx args.head!
          if namespace_ == "Number" && ["isNaN", "isFinite"].contains name then return .boolean
          if namespace_ == "Math" && ["abs", "floor", "trunc", "sqrt"].contains name then
            requireType t .number span
            return .number
          error "A1001" s!"builtin '{namespace_}.{name}' is not supported" span
      let ty ← infer n ctx object
      if ["push", "pop", "set", "delete", "clear"].contains name then checkWrite ctx object
      match ty, name, args with
      | .array t, "push", [arg] => checkExpr n ctx arg t; return .number
      | .array t, "pop", [] => return .union t .undefined
      | .array t, "slice", [a, b] =>
        checkExpr n ctx a .number; checkExpr n ctx b .number; return .array t
      | .array t, "map", [fn] | .array t, "filter", [fn] | .array t, "forEach", [fn] =>
        let ft ← infer n (protect ctx object) fn
        let .function ps r := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [t] && ps != [t, .number] then error "A2002" "callback parameters do not match array element/index types" fn.span
        if name == "filter" then requireType r .boolean fn.span; return .array t
        return if name == "map" then .array r else .void
      | .array t, "reduce", [fn, initial] =>
        let acc ← infer n ctx initial
        let ft ← infer n (protect ctx object) fn
        let .function ps r := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [acc, t] && ps != [acc, t, .number] then error "A2002" "reduce callback parameters do not match" fn.span
        requireType r acc fn.span
        return acc
      | .map k v, "get", [key] => checkExpr n ctx key k; return .union v .undefined
      | .map k _, "has", [key] | .map k _, "delete", [key] => checkExpr n ctx key k; return .boolean
      | .map k v, "set", [key, value] => checkExpr n ctx key k; checkExpr n ctx value v; return ty
      | .map _ _, "clear", [] => return .void
      | .map k v, "forEach", [fn] =>
        let ft ← infer n (protect ctx object) fn
        let .function ps _ := ft | error "A2002" "expected a typed callback" fn.span
        if ps != [v, k] && ps != [v] then error "A2002" "Map callback takes value, then key" fn.span
        return .void
      | .string, "charCodeAt", [i] => checkExpr n ctx i .number; return .number
      | .string, "slice", [a] => checkExpr n ctx a .number; return .string
      | .string, "slice", [a, b] => checkExpr n ctx a .number; checkExpr n ctx b .number; return .string
      | _, _, _ => error "A1001" s!"unsupported method or argument list: {typeName ty}.{name}" span

  def checkStmt (fuel : Nat) (ctx : Context) (stmt : Stmt) : Checked Context := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" stmt.span
    | n + 1 =>
      match stmt with
      | .block stmts _ =>
        let _ ← checkBlock n ctx stmts
        return ctx
      | .let_ mutable name annotation value span =>
        if reserved name || ctx.program.functions.any (fun f => f.name == name) then error "A3004" s!"cannot shadow reserved intrinsic '{name}'" span
        if ctx.bindings.any (fun b => b.name == name) then error "A2005" s!"shadowing or duplicate declaration of '{name}' is not supported" span
        let t ← match annotation with
          | some ty =>
            let ty ← resolve 100 ctx.program ty
            checkExpr n ctx value ty
            pure ty
          | none => infer n ctx value
        if referenceType t then
          match value with
          | .var _ _ | .member _ _ _ | .index _ _ _ =>
            error "A3001" "binding would create an alias to a mutable reference" value.span
          | .call (.member _ "set" _) _ _ => error "A3001" "Map.set returns its receiver; binding it would create an alias" value.span
          | .lambda _ _ _ => error "A3001" "callbacks must appear directly at a supported traversal call" value.span
          | _ => pure ()
        return { ctx with bindings := { name, ty := t, mutable, span } :: ctx.bindings }
      | .assign target value span =>
        checkWrite ctx target
        match target with
        | .var name _ =>
          let b ← binding ctx name target.span
          if !b.mutable then error "A2008" s!"cannot assign to const binding '{name}'" span
          if referenceType b.ty then error "A3001" "reassigning owned references is not yet supported" span
          checkExpr n ctx value b.ty
        | .index object index _ =>
          checkExpr n ctx index .number
          let .array t ← infer n ctx object | error "A2002" "indexed assignment requires an array" span
          checkExpr n ctx value t
        | .member object field _ =>
          let .record fields ← infer n ctx object | error "A3004" "only declared record fields may be assigned" span
          let some t := fields.lookup field | error "A2006" s!"unknown field '{field}'" span
          checkExpr n ctx value t
        | _ => error "A2002" "invalid assignment target" span
        return ctx
      | .expr e _ => let _ ← infer n ctx e; return ctx
      | .if_ c yes no _ =>
        checkExpr n ctx c .boolean
        let _ ← checkStmt n ctx yes
        let _ ← checkStmt n ctx no
        return ctx
      | .while_ c body _ =>
        checkExpr n ctx c .boolean
        let _ ← checkStmt n { ctx with loopDepth := ctx.loopDepth + 1 } body
        return ctx
      | .for_ init c update body _ =>
        let inner ← checkStmt n ctx init
        checkExpr n inner c .boolean
        let _ ← checkStmt n inner update
        let _ ← checkStmt n { inner with loopDepth := inner.loopDepth + 1 } body
        return ctx
      | .return_ e span =>
        checkExpr n ctx e ctx.result
        if referenceType ctx.result then
          match e with
          | .var name _ =>
            let b ← binding ctx name span
            if b.borrowed then error "A3001" "returning a borrowed reference would escape its lifetime" span
          | .array .. | .record .. | .newMap .. => pure ()
          | .call (.var ..) _ _ => pure ()
          | .call (.member _ method _) _ _ =>
            if !["map", "filter", "slice"].contains method then
              error "A3001" "a returned reference must be owned; this method can return its receiver" span
          | _ => error "A3001" "return an owned local variable or a fresh collection" span
        return ctx
      | .break_ span | .continue_ span =>
        if ctx.loopDepth == 0 then error "A2009" "loop control is only valid inside a loop" span
        return ctx

  def checkBlock (fuel : Nat) (ctx : Context) (stmts : List Stmt) : Checked Context := do
    match fuel with
    | 0 => error "A2000" "type checking resource bound exceeded" {}
    | n + 1 =>
      match stmts with
      | [] => return ctx
      | stmt :: rest => checkBlock n (← checkStmt n ctx stmt) rest
end

def returns : Nat → Stmt → Bool
  | 0, _ => false
  | _ + 1, .return_ _ _ => true
  | n + 1, .block ss _ => ss.any (returns n)
  | n + 1, .if_ _ yes no _ => returns n yes && returns n no
  | _, _ => false

def program (p : Program) : Checked Unit := do
  if (p.functions.map Function.name).eraseDups.length != p.functions.length then
    error "A2005" "duplicate function declaration" {}
  if (p.aliases.map Prod.fst).eraseDups.length != p.aliases.length then
    error "A2005" "duplicate type alias" {}
  for f in p.functions do
    if reserved f.name then error "A3004" s!"cannot shadow intrinsic '{f.name}'" f.span
    if (f.params.map Param.name).eraseDups.length != f.params.length then
      error "A2005" "duplicate parameter" f.span
    let bindings ← f.params.mapM fun param => do
      if reserved param.name || p.functions.any (fun f => f.name == param.name) then error "A3004" s!"cannot shadow intrinsic '{param.name}'" param.span
      let t ← resolve 100 p param.ty
      return { name := param.name, ty := t, mutable := true, borrowed := referenceType t, span := param.span : Binding }
    let result ← resolve 100 p f.result
    let _ ← checkStmt 10000 { program := p, bindings, result } f.body
    if result != .void && !returns 10000 f.body then
      error "A2010" s!"function '{f.name}' may fall through without returning a value" f.span

end Check

def frontend (source : String) : Checked Program := do
  let program ← parse source
  Check.program program
  return program

end Ariadne

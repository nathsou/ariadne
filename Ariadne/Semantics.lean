import Ariadne.Value

namespace Ariadne

inductive Control where
  | normal | returned | broke | continued
  deriving Repr, BEq, DecidableEq, Inhabited

structure Completion where
  control : Control := .normal
  value : Value := .undefined
  state : State
  deriving Repr, BEq, Inhabited

def readMember (s : State) (receiver : Value) (field : String) : Result Value := do
  match receiver with
  | .string units =>
    if field == "length" then return .number (Float.Model.ofNat units.length)
    return .stringMethod units field
  | .function namespace_ => return .function (namespace_ ++ "." ++ field)
  | .ref loc =>
    match s.heap[loc]? with
    | some (.array xs) =>
      if field == "length" then return .number (Float.Model.ofNat xs.length)
      return .method loc field
    | some (.map xs) =>
      if field == "size" then return .number (Float.Model.ofNat xs.length)
      return .method loc field
    | some (.record fields) => return (fields.lookup field).getD .undefined
    | _ => throw (.typeError "property access requires a collection or record")
  | _ => throw (.typeError "property access on a non-object")

def readIndex (s : State) (receiver index : Value) : Result Value := do
  let some i := indexOf index | return .undefined
  match receiver with
  | .string units => return (units[i]?.map fun u => Value.string [u]).getD .undefined
  | .ref loc =>
    match s.heap[loc]? with
    | some (.array xs) => return xs[i]?.getD .undefined
    | _ => throw (.typeError "indexed access requires an array")
  | _ => throw (.typeError "indexed access requires an array or string")

def invokeScalar (name : String) (args : List Value) : Result Value := do
  match name, args with
  | "Number.isNaN", [.number x] => return .boolean x.isNaN
  | "Number.isNaN", [_] => return .boolean false
  | "Number.isFinite", [.number x] => return .boolean x.isFinite
  | "Number.isFinite", [_] => return .boolean false
  | "Math.abs", [.number x] => return .number x.abs
  | "Math.sqrt", [.number x] => return .number x.sqrt
  | "Math.trunc", [.number x] =>
    if !x.isFinite || x == Float.Model.ofNat 0 then return .number x
    let i := x.unpack.toInt 0 0
    if i == 0 && x < Float.Model.ofNat 0 then
      return .number (Float.Model.ofNat 0).neg
    return .number (Float.Model.ofInt i)
  | "Math.floor", [.number x] =>
    if !x.isFinite || x == Float.Model.ofNat 0 then return .number x
    let i := x.unpack.toInt 0 0
    return .number (Float.Model.ofInt (if Float.Model.ofInt i > x then i - 1 else i))
  | "BigInt", [.number x] =>
    let i := x.unpack.toInt 0 0
    if x.isFinite && Float.Model.ofInt i == x then return .bigint i
    throw (.rangeError "BigInt requires a finite integer")
  | "BigInt", [.bigint x] => return .bigint x
  | "Number", [.bigint x] => return .number (Float.Model.ofInt x)
  | "Number", [.number x] => return .number x
  | _, _ => throw (.typeError s!"invalid call to '{name}'")

def sliceBound (v : Value) (length : Nat) : Nat :=
  match v with
  | .number x =>
    let i := x.unpack.toInt (-(Int.ofNat length)) length
    if i < 0 then (max 0 (Int.ofNat length + i)).toNat else min i.toNat length
  | _ => 0

def invokeString (units : JSString) (name : String) (args : List Value) : Result Value := do
  match name, args with
  | "charCodeAt", [index] =>
    -- Index arguments accepted by the checker are numbers; NaN becomes zero.
    let i := match index with | .number x => x.unpack.toInt (-1) (-1) | _ => -1
    if i < 0 then return .number Float.Model.nan
    return .number ((units[i.toNat]?.map fun u => Float.Model.ofNat u.toNat).getD Float.Model.nan)
  | "slice", [start] => return .string (units.drop (sliceBound start units.length))
  | "slice", [start, stop] =>
    let first := sliceBound start units.length
    let last := sliceBound stop units.length
    return .string ((units.drop first).take (last - first))
  | _, _ => throw (.typeError s!"invalid string method '{name}'")

mutual
  /-- Executable source semantics. Fuel bounds recursive evaluation depth, not JS steps. -/
  def evalExpr (program : Program) (fuel : Nat) (s : State) (expr : Expr) : Result (Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match expr with
      | .literal value _ => return (Value.ofLiteral value, s)
      | .var name _ =>
        if s.env.any (fun p => p.1 == name) then return (← s.lookup name, s)
        if name == "NaN" then return (.number Float.Model.nan, s)
        if name == "Infinity" then return (.number Float.Model.inf, s)
        return (.function name, s)
      | .unary op arg _ =>
        let (v, s) ← evalExpr program n s arg
        return (← unary op v, s)
      | .binary op left right _ =>
        let (a, s) ← evalExpr program n s left
        if op == "&&" && !a.truthy then return (a, s)
        if op == "||" && a.truthy then return (a, s)
        if op == "??" && a != .undefined && a != .null then return (a, s)
        let (b, s) ← evalExpr program n s right
        if ["&&", "||", "??"].contains op then return (b, s)
        return (← binary op a b, s)
      | .conditional condition yes no _ =>
        let (v, s) ← evalExpr program n s condition
        evalExpr program n s (if v.truthy then yes else no)
      | .call callee args _ =>
        let (fn, s) ← evalExpr program n s callee
        let (args, s) ← evalArgs program n s args
        apply program n s fn args
      | .member object field _ =>
        let (v, s) ← evalExpr program n s object
        return (← readMember s v field, s)
      | .index object index _ =>
        let (v, s) ← evalExpr program n s object
        let (i, s) ← evalExpr program n s index
        return (← readIndex s v i, s)
      | .array elements _ =>
        let (xs, s) ← evalArgs program n s elements
        let (loc, s) := s.alloc (.array xs)
        return (.ref loc, s)
      | .record fields _ =>
        let (xs, s) ← evalArgs program n s (fields.map Prod.snd)
        let (loc, s) := s.alloc (.record ((fields.map Prod.fst).zip xs))
        return (.ref loc, s)
      | .newMap _ _ _ =>
        let (loc, s) := s.alloc (.map [])
        return (.ref loc, s)
      | .lambda params body _ =>
        let (loc, s) := s.alloc (.closure params body s.env)
        return (.ref loc, s)

  def evalArgs (program : Program) (fuel : Nat) (s : State) (exprs : List Expr) : Result (List Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match exprs with
      | [] => return ([], s)
      | e :: rest =>
        let (v, s) ← evalExpr program n s e
        let (vs, s) ← evalArgs program n s rest
        return (v :: vs, s)

  def apply (program : Program) (fuel : Nat) (s : State) (fn : Value) (args : List Value) : Result (Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match fn with
      | .function name =>
        if let some f := program.functions.find? (fun f => f.name == name) then
          callBody program n s [] f.params f.body args
        else return (← invokeScalar name args, s)
      | .ref loc =>
        match s.heap[loc]? with
        | some (.closure params body captured) => callBody program n s captured params body args
        | _ => throw (.typeError "value is not callable")
      | .stringMethod units name => return (← invokeString units name args, s)
      | .method loc name =>
        match s.heap[loc]? with
        | some (.array xs) =>
          match name, args with
          | "push", [v] =>
            if xs.length ≥ 4294967295 then throw (.rangeError "maximum array length exceeded")
            return (.number (Float.Model.ofNat (xs.length + 1)), ← s.write loc (.array (xs ++ [v])))
          | "pop", [] => return (xs.getLast?.getD .undefined, ← s.write loc (.array xs.dropLast))
          | "slice", [start, stop] =>
            let first := sliceBound start xs.length
            let last := sliceBound stop xs.length
            let (out, s) := s.alloc (.array ((xs.drop first).take (last - first)))
            return (.ref out, s)
          | "map", [callback] | "filter", [callback] | "forEach", [callback] =>
            let (ys, s) ← traverse program n s callback xs 0 name
            if name == "forEach" then return (.undefined, s)
            let (out, s) := s.alloc (.array ys)
            return (.ref out, s)
          | "reduce", [callback, initial] => reduce program n s callback xs initial 0
          | _, _ => throw (.typeError s!"invalid array method '{name}'")
        | some (.map entries) =>
          match name, args with
          | "get", [key] => return (mapGet entries key, s)
          | "has", [key] => return (.boolean (mapHas entries key), s)
          | "set", [key, value] => return (.ref loc, ← s.write loc (.map (mapSet entries key value)))
          | "delete", [key] => return (.boolean (mapHas entries key), ← s.write loc (.map (mapDelete entries key)))
          | "clear", [] => return (.undefined, ← s.write loc (.map []))
          | "forEach", [callback] =>
            let s ← mapTraverse program n s callback entries
            return (.undefined, s)
          | _, _ => throw (.typeError s!"invalid Map method '{name}'")
        | _ => throw (.typeError "invalid method receiver")
      | _ => throw (.typeError "value is not callable")

  def callBody (program : Program) (fuel : Nat) (s : State) (captured : Env)
      (params : List Param) (body : Stmt) (args : List Value) : Result (Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      let caller := s.env
      let s := (params.zip args).foldl (fun s (p, v) => s.declare p.name v) { s with env := captured }
      let out ← exec program n s body
      if out.control == .broke || out.control == .continued then throw (.invariant "loop control escaped a function")
      return (out.value, { out.state with env := caller })

  def traverse (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (xs : List Value) (index : Nat) (mode : String) : Result (List Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match xs with
      | [] => return ([], s)
      | x :: rest =>
        let (y, s) ← apply program n s callback [x, .number (Float.Model.ofNat index)]
        let (ys, s) ← traverse program n s callback rest (index + 1) mode
        return (if mode == "filter" then (if y.truthy then x :: ys else ys) else y :: ys, s)

  def reduce (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (xs : List Value) (acc : Value) (index : Nat) : Result (Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match xs with
      | [] => return (acc, s)
      | x :: rest =>
        let (acc, s) ← apply program n s callback [acc, x, .number (Float.Model.ofNat index)]
        reduce program n s callback rest acc (index + 1)

  def mapTraverse (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (entries : List (Value × Value)) : Result State := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match entries with
      | [] => return s
      | (key, value) :: rest =>
        let (_, s) ← apply program n s callback [value, key]
        mapTraverse program n s callback rest

  def assignTarget (program : Program) (fuel : Nat) (s : State) (target rhs : Expr) : Result State := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match target with
      | .var name _ =>
        let (value, s) ← evalExpr program n s rhs
        s.assign name value
      | .index object index _ =>
        -- Evaluate the reference before the RHS, as required by ECMAScript.
        let (receiver, s) ← evalExpr program n s object
        let (index, s) ← evalExpr program n s index
        let (value, s) ← evalExpr program n s rhs
        let .ref loc := receiver | throw (.typeError "assignment requires an array")
        let some i := indexOf index | throw (.invariant "array writes require a nonnegative integer index")
        let some (.array xs) := s.heap[loc]? | throw (.typeError "assignment requires an array")
        if i > xs.length then throw (.invariant "array write would introduce holes")
        if i ≥ 4294967295 then throw (.invariant "array write exceeds the dense-array index range")
        s.write loc (.array (if i == xs.length then xs ++ [value] else xs.set i value))
      | .member object field _ =>
        let (receiver, s) ← evalExpr program n s object
        let (value, s) ← evalExpr program n s rhs
        let .ref loc := receiver | throw (.typeError "assignment requires a record")
        let some (.record fields) := s.heap[loc]? | throw (.typeError "assignment requires a record")
        s.write loc (.record (fields.map fun (k, v) => (k, if k == field then value else v)))
      | _ => throw (.invariant "invalid assignment target")

  def exec (program : Program) (fuel : Nat) (s : State) (stmt : Stmt) : Result Completion := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match stmt with
      | .block statements _ =>
        let outer := s.env
        let out ← execBlock program n s statements
        return { out with state := { out.state with env := outer } }
      | .let_ _ name _ value _ =>
        let (v, s) ← evalExpr program n s value
        return { state := s.declare name v }
      | .assign target value _ => return { state := ← assignTarget program n s target value }
      | .expr value _ =>
        let (_, s) ← evalExpr program n s value
        return { state := s }
      | .if_ condition yes no _ =>
        let (v, s) ← evalExpr program n s condition
        exec program n s (if v.truthy then yes else no)
      | .while_ condition body _ => loop program n s condition body none
      | .for_ init condition update body _ =>
        let outer := s.env
        let initial ← exec program n s init
        let out ← loop program n initial.state condition body (some update)
        return { out with state := { out.state with env := outer } }
      | .return_ value _ =>
        let (v, s) ← evalExpr program n s value
        return { control := .returned, value := v, state := s }
      | .break_ _ => return { control := .broke, state := s }
      | .continue_ _ => return { control := .continued, state := s }

  def execBlock (program : Program) (fuel : Nat) (s : State) (stmts : List Stmt) : Result Completion := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match stmts with
      | [] => return { state := s }
      | stmt :: rest =>
        let out ← exec program n s stmt
        if out.control != .normal then return out
        execBlock program n out.state rest

  def loop (program : Program) (fuel : Nat) (s : State) (condition : Expr)
      (body : Stmt) (update : Option Stmt) : Result Completion := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      let (v, s) ← evalExpr program n s condition
      if !v.truthy then return { state := s }
      let out ← exec program n s body
      if out.control == .returned then return out
      if out.control == .broke then return { state := out.state }
      let s ← match update with
        | none => pure out.state
        | some stmt => (exec program n out.state stmt).map Completion.state
      loop program n s condition body update
end

def runState (program : Program) (name : String) (fuel : Nat) (args : List Value) : Result (Value × State) :=
  apply program fuel {} (.function name) args

def run (program : Program) (name : String) (fuel : Nat) (args : List Value) : Result Value :=
  (runState program name fuel args).map Prod.fst

/-- Terminating behavior is existential in the evaluator budget. -/
def Returns (program : Program) (name : String) (args : List Value) (value : Value) : Prop :=
  ∃ fuel, run program name fuel args = .ok value

end Ariadne

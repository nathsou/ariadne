import Ariadne.Builtins

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
    | some (.set xs) =>
      if field == "size" then return .number (Float.Model.ofNat xs.length)
      return .method loc field
    | some (.instance_ _ fields) =>
      if let some value := fields.lookup field then return value
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
  | "#templateString", [value] => return .string (← Builtins.scalarString value)
  | "Math.min", values => Builtins.extremum true values
  | "Math.max", values => Builtins.extremum false values
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
  | "charCodeAt", [] =>
    return .number ((units[0]?.map fun u => Float.Model.ofNat u.toNat).getD Float.Model.nan)
  | "charCodeAt", [index] =>
    -- Index arguments accepted by the checker are numbers; NaN becomes zero.
    let i := match index with | .number x => x.unpack.toInt (-1) (-1) | _ => -1
    if i < 0 then return .number Float.Model.nan
    return .number ((units[i.toNat]?.map fun u => Float.Model.ofNat u.toNat).getD Float.Model.nan)
  | "slice", [] => return .string units
  | "slice", [start] => return .string (units.drop (sliceBound start units.length))
  | "slice", [start, stop] =>
    let first := sliceBound start units.length
    let last := sliceBound stop units.length
    return .string ((units.drop first).take (last - first))
  | "startsWith", [.string needle] | "endsWith", [.string needle] |
      "includes", [.string needle] | "indexOf", [.string needle] =>
    return Builtins.stringSearch units name needle (if name == "endsWith" then units.length else 0)
  | "startsWith", [.string needle, pos] | "endsWith", [.string needle, pos] |
      "includes", [.string needle, pos] | "indexOf", [.string needle, pos] =>
    return Builtins.stringSearch units name needle (Builtins.position pos units.length)
  | _, _ => throw (.typeError s!"invalid string method '{name}'")

/-- Allocate pair arrays in insertion order for Map entries/iteration. -/
def entryArray (s : State) (entries : List (Value × Value)) : List Value × State :=
  entries.foldl (fun (xs, s) (k, v) =>
    let (loc, s) := s.alloc (.array [k, v])
    (xs ++ [.ref loc], s)) ([], s)

def iterable (s : State) (value : Value) : Result (List Value × State) := do
  let .ref loc := value | throw (.typeError "iteration requires a collection")
  match s.heap[loc]? with
  | some (.array xs) | some (.set xs) | some (.iterator xs) => return (xs, s)
  | some (.map entries) => return entryArray s entries
  | _ => throw (.typeError "iteration requires a collection")

/-- Object spread and repeated properties use the last value without moving keys. -/
def fieldSet (fields : List (String × Value)) (key : String) (value : Value) : List (String × Value) :=
  if fields.any (fun p => p.1 == key) then
    fields.map fun (k, v) => (k, if k == key then value else v)
  else fields ++ [(key, value)]

mutual
  /-- Executable source semantics. Fuel bounds recursive evaluation depth, not JS steps. -/
  def evalExpr (program : Program) : Nat → State → Expr → Result (Value × State)
    | 0, _, _ => .error .timeout
    | _n + 1, s, .literal value _ => do return (Value.ofLiteral value, s)
    | _n + 1, s, .var name _ => do
      if s.env.any (fun p => p.1 == name) then return (← s.lookup name, s)
      if name == "NaN" then return (.number Float.Model.nan, s)
      if name == "Infinity" then return (.number Float.Model.inf, s)
      return (.function name, s)
    | n + 1, s, .unary op arg _ => do
      let (v, s) ← evalExpr program n s arg
      return (← unary op v, s)
    | n + 1, s, .binary op left right _ => do
      let (a, s) ← evalExpr program n s left
      if op == "&&" && !a.truthy then return (a, s)
      if op == "||" && a.truthy then return (a, s)
      if op == "??" && a != .undefined && a != .null then return (a, s)
      let (b, s) ← evalExpr program n s right
      if ["&&", "||", "??"].contains op then return (b, s)
      return (← binary op a b, s)
    | n + 1, s, .conditional condition yes no _ => do
      let (v, s) ← evalExpr program n s condition
      evalExpr program n s (if v.truthy then yes else no)
    | n + 1, s, .call callee args _ => do
      let (fn, s) ← evalExpr program n s callee
      let (args, s) ← evalArgs program n s args
      apply program n s fn args
    | n + 1, s, .member object field _ => do
      let (v, s) ← evalExpr program n s object
      return (← readMember s v field, s)
    | n + 1, s, .index object index _ => do
      let (v, s) ← evalExpr program n s object
      let (i, s) ← evalExpr program n s index
      return (← readIndex s v i, s)
    | n + 1, s, .array elements _ => do
      let (xs, s) ← evalElements program n s elements
      let (loc, s) := s.alloc (.array xs)
      return (.ref loc, s)
    | n + 1, s, .record fields _ => do
      let (xs, s) ← evalFields program n s fields []
      let (loc, s) := s.alloc (.record xs)
      return (.ref loc, s)
    | _n + 1, s, .newMap _ _ _ => do
      let (loc, s) := s.alloc (.map [])
      return (.ref loc, s)
    | _n + 1, s, .newSet _ _ => do
      let (loc, s) := s.alloc (.set [])
      return (.ref loc, s)
    | n + 1, s, .newClass name args _ => do
      let some c := program.classes.find? (·.name == name)
        | throw (.typeError "unknown class")
      let (args, s) ← evalArgs program n s args
      let (fields, s) ← evalFields program n s (c.fields.map fun f => (f.name, f.value)) []
      let (loc, s) := s.alloc (.instance_ name fields)
      match c.constructor_ with
      | none => return (.ref loc, s)
      | some ctor =>
        let (_, s) ← callBody program n s []
          ({ name := "this", ty := .class_ name } :: ctor.params) ctor.body (.ref loc :: args)
        return (.ref loc, s)
    | _ + 1, _, .spread _ _ => .error (.invariant "spread outside collection literal")
    | _n + 1, s, .lambda params body _ => do
      let (loc, s) := s.alloc (.closure params body s.env)
      return (.ref loc, s)
  termination_by structural fuel _ _ => fuel


  def evalElements (program : Program) : Nat → State → List Expr → Result (List Value × State)
    | 0, _, _ => .error .timeout
    | _ + 1, s, [] => .ok ([], s)
    | n + 1, s, e :: rest => do
      let (head, s) ← match e with
        | .spread source _ => do
          let (value, s) ← evalExpr program n s source
          iterable s value
        | _ => do
          let (value, s) ← evalExpr program n s e
          pure ([value], s)
      let (tail, s) ← evalElements program n s rest
      return (head ++ tail, s)
  termination_by structural fuel _ _ => fuel


  def evalFields (program : Program) : Nat → State → List (String × Expr) →
      List (String × Value) → Result (List (String × Value) × State)
    | 0, _, _, _ => .error .timeout
    | _ + 1, s, [], acc => .ok (acc, s)
    | n + 1, s, (key, e) :: rest, acc => do
      let (value, s) ← evalExpr program n s e
      let acc ← if key == "" then do
        let .ref loc := value | throw (.typeError "object spread requires a record")
        let fields ← match s.heap[loc]? with
          | some (.record fields) | some (.instance_ _ fields) => pure fields
          | _ => throw (.typeError "object spread requires a record")
        pure (fields.foldl (fun fs (k, v) => fieldSet fs k v) acc)
        else pure (fieldSet acc key value)
      evalFields program n s rest acc
  termination_by structural fuel _ _ _ => fuel


  def evalArgs (program : Program) : Nat → State → List Expr → Result (List Value × State)
    | 0, _, _ => .error .timeout
    | _n + 1, s, [] => do return ([], s)
    | n + 1, s, e :: rest => do
      let (v, s) ← evalExpr program n s e
      let (vs, s) ← evalArgs program n s rest
      return (v :: vs, s)
  termination_by structural fuel _ _ => fuel


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
          | "slice", [] =>
            let (out, s) := s.alloc (.array xs)
            return (.ref out, s)
          | "slice", [start] =>
            let (out, s) := s.alloc (.array (xs.drop (sliceBound start xs.length)))
            return (.ref out, s)
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
          | "some", [callback] | "every", [callback] | "find", [callback] | "findIndex", [callback] =>
            search program n s callback xs 0 name
          | "toSorted", [callback] =>
            let (ys, s) ← sort program n s callback xs
            let (out, s) := s.alloc (.array ys)
            return (.ref out, s)
          | "concat", values =>
            let ys := values.flatMap fun v => match v with
              | .ref loc => match s.heap[loc]? with | some (.array ys) => ys | _ => [v]
              | _ => [v]
            let (out, s) := s.alloc (.array (xs ++ ys))
            return (.ref out, s)
          | "join", [] => return (.string (← Builtins.join xs [44]), s)
          | "join", [.string sep] => return (.string (← Builtins.join xs sep), s)
          | "includes", [value] => return (.boolean (xs.any (sameValueZero · value)), s)
          | "includes", [value, start] =>
            return (.boolean ((xs.drop (sliceBound start xs.length)).any (sameValueZero · value)), s)
          | "indexOf", [value] =>
            return (.number (Float.Model.ofInt ((xs.findIdx? (strictEqual · value)).map Int.ofNat |>.getD (-1))), s)
          | "indexOf", [value, start] =>
            let first := sliceBound start xs.length
            let found := (xs.drop first).findIdx? (strictEqual · value)
            return (.number (Float.Model.ofInt (found.map (fun i => Int.ofNat (first + i)) |>.getD (-1))), s)
          | "toReversed", [] =>
            let (out, s) := s.alloc (.array xs.reverse)
            return (.ref out, s)
          | "entries", [] =>
            let (entries, s) := entryArray s (xs.zipIdx.map fun (v, i) => (.number (Float.Model.ofNat i), v))
            let (out, s) := s.alloc (.iterator entries)
            return (.ref out, s)
          | _, _ => throw (.typeError s!"invalid array method '{name}'")
        | some (.map entries) =>
          match name, args with
          | "get", [key] => return (mapGet entries key, s)
          | "has", [key] => return (.boolean (mapHas entries key), s)
          | "set", [key, value] => return (.ref loc, ← s.write loc (.map (mapSet entries key value)))
          | "delete", [key] => return (.boolean (mapHas entries key), ← s.write loc (.map (mapDelete entries key)))
          | "clear", [] => return (.undefined, ← s.write loc (.map []))
          | "keys", [] | "values", [] =>
            let (out, s) := s.alloc (.iterator (entries.map (if name == "keys" then Prod.fst else Prod.snd)))
            return (.ref out, s)
          | "entries", [] =>
            let (entries, s) := entryArray s entries
            let (out, s) := s.alloc (.iterator entries)
            return (.ref out, s)
          | "forEach", [callback] =>
            let s ← mapTraverse program n s callback entries
            return (.undefined, s)
          | _, _ => throw (.typeError s!"invalid Map method '{name}'")
        | some (.set xs) =>
          match name, args with
          | "has", [v] => return (.boolean (xs.any (sameValueZero · v)), s)
          | "add", [v] => return (.ref loc, ← s.write loc (.set
              (if xs.any (sameValueZero · v) then xs else xs ++ [canonicalKey v])))
          | "delete", [v] => return (.boolean (xs.any (sameValueZero · v)),
              ← s.write loc (.set (xs.filter fun x => !sameValueZero x v)))
          | "clear", [] => return (.undefined, ← s.write loc (.set []))
          | "keys", [] | "values", [] =>
            let (out, s) := s.alloc (.iterator xs)
            return (.ref out, s)
          | "entries", [] =>
            let (entries, s) := entryArray s (xs.map fun x => (x, x))
            let (out, s) := s.alloc (.iterator entries)
            return (.ref out, s)
          | _, _ => throw (.typeError "invalid Set method")
        | some (.instance_ className _) =>
          let some c := program.classes.find? (·.name == className)
            | throw (.typeError "unknown class")
          let some method := c.methods.find? (·.name == name)
            | throw (.typeError "unknown method")
          callBody program n s [] ({ name := "this", ty := .class_ className } :: method.params)
            method.body (.ref loc :: args)
        | _ => throw (.typeError "invalid method receiver")
      | _ => throw (.typeError "value is not callable")
  termination_by structural fuel


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
  termination_by structural fuel


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
  termination_by structural fuel


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
  termination_by structural fuel


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
  termination_by structural fuel


  /-- Searches stop as soon as the result is determined. -/
  def search (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (xs : List Value) (index : Nat) (mode : String) : Result (Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 => match xs with
      | [] => return (if mode == "find" then .undefined else if mode == "findIndex" then
          .number (Float.Model.ofInt (-1)) else .boolean (mode == "every"), s)
      | x :: rest =>
        let (answer, s) ← apply program n s callback [x, .number (Float.Model.ofNat index)]
        if answer.truthy != (mode == "every") then
          return (if mode == "find" then x else if mode == "findIndex" then
            .number (Float.Model.ofNat index) else .boolean (mode != "every"), s)
        search program n s callback rest (index + 1) mode
  termination_by structural fuel


  /-- A stable merge: NaN comparator results are treated as zero. -/
  def merge (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (xs ys : List Value) : Result (List Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 => match xs, ys with
      | [], ys => return (ys, s)
      | xs, [] => return (xs, s)
      | x :: xs, y :: ys =>
        -- Undefined elements sort last without calling the user comparator.
        let (comparison, s) ← if x == .undefined then
            pure (.number (Float.Model.ofNat (if y == .undefined then 0 else 1)), s)
          else if y == .undefined then pure (.number (Float.Model.ofInt (-1)), s)
          else apply program n s callback [x, y]
        let .number cmp := comparison | throw (.typeError "sort comparator must return a number")
        if cmp > Float.Model.ofNat 0 then
          let (zs, s) ← merge program n s callback (x :: xs) ys
          return (y :: zs, s)
        else
          let (zs, s) ← merge program n s callback xs (y :: ys)
          return (x :: zs, s)
  termination_by structural fuel


  def sort (program : Program) (fuel : Nat) (s : State) (callback : Value)
      (xs : List Value) : Result (List Value × State) := do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      if xs.length < 2 then return (xs, s)
      let half := xs.length / 2
      let (left, s) ← sort program n s callback (xs.take half)
      let (right, s) ← sort program n s callback (xs.drop half)
      merge program n s callback left right
  termination_by structural fuel

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
        match s.heap[loc]? with
        | some (.record fields) => s.write loc (.record (fieldSet fields field value))
        | some (.instance_ name fields) => s.write loc (.instance_ name (fieldSet fields field value))
        | _ => throw (.typeError "assignment requires a record")
      | _ => throw (.invariant "invalid assignment target")
  termination_by structural fuel


  def exec (program : Program) : Nat → State → Stmt → Result Completion
    | 0, _, _ => .error .timeout
    | n + 1, s, .block statements _ => do
      let outer := s.env
      let out ← execBlock program n s statements
      return { out with state := { out.state with env := outer } }
    | n + 1, s, .let_ _ name _ value _ => do
      let (v, s) ← evalExpr program n s value
      return { state := s.declare name v }
    | n + 1, s, .assign target value _ => do return { state := ← assignTarget program n s target value }
    | n + 1, s, .expr value _ => do
      let (_, s) ← evalExpr program n s value
      return { state := s }
    | n + 1, s, .if_ condition yes no _ => do
      let (v, s) ← evalExpr program n s condition
      exec program n s (if v.truthy then yes else no)
    | n + 1, s, .while_ condition body _ => do loop program n s condition body none
    | n + 1, s, .for_ init condition update body _ => do
      let outer := s.env
      let initial ← exec program n s init
      let out ← loop program n initial.state condition body (some update)
      return { out with state := { out.state with env := outer } }
    | n + 1, s, .measured _ body _ => exec program n s body
    | n + 1, s, .forOf _ name collection body _ => do
      let (value, s) ← evalExpr program n s collection
      let (xs, s) ← iterable s value
      eachBody program n s name body xs
    | n + 1, s, .switch_ value cases _ => do
      let (value, s) ← evalExpr program n s value
      let outer := s.env
      let selected ← selectCase program n s value cases 0 none
      match selected with
      | none => return { state := s }
      | some index =>
        let out ← execBlock program n s ((cases.drop index).flatMap Prod.snd)
        return { out with control := if out.control == .broke then .normal else out.control, state := { out.state with env := outer } }
    | n + 1, s, .return_ value _ => do
      let (v, s) ← evalExpr program n s value
      return { control := .returned, value := v, state := s }
    | _n + 1, s, .break_ _ => do return { control := .broke, state := s }
    | _n + 1, s, .continue_ _ => do return { control := .continued, state := s }
  termination_by structural fuel _ _ => fuel


  def eachBody (program : Program) : Nat → State → String → Stmt → List Value → Result Completion
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, s, _, _, [] => .ok { state := s }
    | n + 1, s, name, body, x :: xs => do
      let out ← exec program n (s.declare name x) body
      let out := { out with state := { out.state with env := s.env } }
      if out.control == .returned then return out
      if out.control == .broke then return { state := out.state }
      eachBody program n out.state name body xs
  termination_by structural fuel _ _ _ _ => fuel


  /-- Case expressions are restricted to literals by the checker, hence effect-free. -/
  def selectCase (program : Program) : Nat → State → Value → List (Option Expr × List Stmt) →
      Nat → Option Nat → Result (Option Nat)
    | 0, _, _, _, _, _ => .error .timeout
    | _ + 1, _, _, [], _, fallback => .ok fallback
    | n + 1, s, value, (label, _) :: cases, index, fallback => do
      match label with
      | none => selectCase program n s value cases (index + 1) (some index)
      | some label =>
        let (v, _) ← evalExpr program n s label
        if strictEqual value v then return some index
        selectCase program n s value cases (index + 1) fallback
  termination_by structural fuel _ _ _ _ _ => fuel


  def execBlock (program : Program) : Nat → State → List Stmt → Result Completion
    | 0, _, _ => .error .timeout
    | _n + 1, s, [] => do return { state := s }
    | n + 1, s, stmt :: rest => do
      let out ← exec program n s stmt
      if out.control != .normal then return out
      execBlock program n out.state rest
  termination_by structural fuel _ _ => fuel


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
  termination_by structural fuel

end

def runState (program : Program) (name : String) (fuel : Nat) (args : List Value) : Result (Value × State) :=
  apply program fuel {} (.function name) args

def run (program : Program) (name : String) (fuel : Nat) (args : List Value) : Result Value :=
  (runState program name fuel args).map Prod.fst

/-- Terminating behavior is existential in the evaluator budget. -/
def Returns (program : Program) (name : String) (args : List Value) (value : Value) : Prop :=
  ∃ fuel, run program name fuel args = .ok value

end Ariadne

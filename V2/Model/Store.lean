import V2.Model.Eval

/-!
# The store model of a class (L8)

The value model (`Eval.lean`) keeps the object a method runs on in the binding
`this`: a method called as a statement gets a copy of it, and the caller's binding
is replaced by the copy the method leaves; a field's map is changed by rebinding
`this`. JavaScript has one object, changed in place and shared with every method
called on it.

This model is closer to JavaScript. The object's state is a **store**, one value
threaded through the statements: `this.f.set(k, v)` changes the store, and a method
called as a statement runs on the same store, so its changes are simply there when
it returns. The environment keeps a placeholder binding for `this` (it marks that a
method is running); nothing reads it. Expressions see the current store: they are
evaluated by the value model in the environment where `this` is the store
(`fill`), which is exact because nothing in an expression changes the state (an
expression may only call a method that changes no state, `Program.scoped`).

`V2/Proof/Store.lean` proves that both models give the same result for every method
of a program that passes the static check (`runMethod_store`), so the value model's
treatment of `this` is a theorem, not an assumption.
-/

namespace V2

/-- The environment where every `this` binding is the store `σ`. -/
def fill (σ : JSValue) (env : Env) : Env := env.map fun (x, v) => if x = "this" then (x, σ) else (x, v)

def Outcome.fill (σ : JSValue) : Outcome → Outcome
  | .normal env => .normal (V2.fill σ env)
  | .returned v env => .returned v (V2.fill σ env)
  | .broke env => .broke (V2.fill σ env)
  | .continued env => .continued (V2.fill σ env)

/-- The store, where a method is running (the environment binds `this`). -/
def storeOf (σ : JSValue) (env : Env) : Except Fault JSValue :=
  if (env.lookup "this").isSome then .ok σ else .error (.referenceError "this")

/-- The store with the `Map` in field `f` replaced. -/
def storeSet (σ : JSValue) (env : Env) (f : String) (kvs : List (JSString × JSValue)) : Except Fault JSValue :=
  match σ with
  | .record fs => if (env.lookup "this").isSome then .ok (.record (upsert fs f (.map kvs)))
      else .error (.referenceError "this")
  | _ => .error (.referenceError "this")

mutual
  /-- Statements, changing the store `σ` in place. -/
  def sExecStmts (p : Program) : Nat → JSValue → Env → List Stmt → Except Fault (Outcome × JSValue)
    | 0, _, _, _ => .error .timeout
    | _ + 1, σ, env, [] => .ok (.normal env, σ)
    | n + 1, σ, env, s :: rest => do
      match ← sExecStmt p n σ env s with
      | (.normal env', σ') => sExecStmts p n σ' env' rest
      | o => .ok o

  def sExecStmt (p : Program) : Nat → JSValue → Env → Stmt → Except Fault (Outcome × JSValue)
    | 0, _, _, _ => .error .timeout
    | n + 1, σ, env, .const x e | n + 1, σ, env, .let_ x e => do
      let v ← evalExpr p n (fill σ env) e
      return (.normal ((x, v) :: env), σ)
    | n + 1, σ, env, .assign x e => do
      let v ← evalExpr p n (fill σ env) e
      return (.normal (← assign x v env), σ)
    | n + 1, σ, env, .ret e => do
      return (.returned (← evalExpr p n (fill σ env) e) env, σ)
    | n + 1, σ, env, .ite c yes no => do
      let branch ← match ← evalExpr p n (fill σ env) c with
        | .bool true => .ok yes
        | .bool false => .ok no
        | _ => .error (.unsupported "condition")
      let (o, σ') ← sExecStmts p n σ env branch
      return (o.restore env, σ')
    | n + 1, σ, env, .block ss => do
      let (o, σ') ← sExecStmts p n σ env ss
      return (o.restore env, σ')
    | n + 1, σ, env, .switch e cases => do
      let v ← evalExpr p n (fill σ env) e
      match ← findCase p n (fill σ env) v cases 0 with
      | none => .ok (.normal env, σ)
      | some i =>
        let (o, σ') ← sExecStmts p n σ env ((cases.drop i).flatMap (·.2))
        match o.restore env with
        | .broke env' => .ok (.normal env', σ')
        | o => .ok (o, σ')
    | _ + 1, σ, env, .brk => .ok (.broke env, σ)
    | _ + 1, σ, env, .cont => .ok (.continued env, σ)
    | n + 1, σ, env, .forOf x e body => do
      match ← evalExpr p n (fill σ env) e with
      | .array xs => sLoop p n σ env (xs.map fun v => [(x, v)]) body
      | _ => .error (.unsupported "for-of over a non-array")
    | n + 1, σ, env, .forEntries i x e body => do
      match ← evalExpr p n (fill σ env) e with
      | .array xs => sLoop p n σ env (entryBindings i x xs) body
      | _ => .error (.unsupported "entries of a non-array")
    | n + 1, σ, env, .forRange i k body => do
      match (fill σ env).lookup k with
      | some (.number m) => sLoop p n σ env (rangeBindings i (min m n)) body
      | some _ => .error (.unsupported "a counted loop's bound that is not a number")
      | none => .error (.referenceError k)
    | n + 1, σ, env, .stateSet f k v => do
      let kvs ← stateMap (fill σ env) f
      let key ← mapKey (← evalExpr p n (fill σ env) k)
      let w ← evalExpr p n (fill σ env) v
      return (.normal env, ← storeSet σ env f (mapPut kvs key w))
    | n + 1, σ, env, .stateDelete f k => do
      let kvs ← stateMap (fill σ env) f
      let key ← mapKey (← evalExpr p n (fill σ env) k)
      return (.normal env, ← storeSet σ env f (mapDel kvs key))
    | n + 1, σ, env, .callThis m args => do
      let vs ← evalArgs p n (fill σ env) args
      let σ ← storeOf σ env
      -- The method runs on the same store: its changes are there when it returns.
      let (_, σ') ← sCallState p n m σ vs
      return (.normal env, σ')

  def sLoop (p : Program) : Nat → JSValue → Env → List Env → List Stmt → Except Fault (Outcome × JSValue)
    | 0, _, _, _, _ => .error .timeout
    | _ + 1, σ, env, [], _ => .ok (.normal env, σ)
    | n + 1, σ, env, bs :: rest, body => do
      let (o, σ') ← sExecStmts p n σ (bs ++ env) body
      match o.restore env with
      | .returned v env' => .ok (.returned v env', σ')
      | .broke env' => .ok (.normal env', σ')
      | .normal env' | .continued env' => sLoop p n σ' env' rest body

  /-- Call a method on the store: its result and the store when it ends. -/
  def sCallState (p : Program) : Nat → String → JSValue → List JSValue → Except Fault (JSValue × JSValue)
    | 0, _, _, _ => .error .timeout
    | n + 1, m, σ, vs => match p.find? (·.name == m) with
      | none => .error (.referenceError m)
      | some fn => if fn.method then do
          match ← sExecStmts p n σ (bindParams fn.params (.undefined :: vs)) fn.body with
          | (.returned v env, σ') => return (v, ← storeOf σ' env)
          | (.normal env, σ') => return (.undefined, ← storeOf σ' env)
          | _ => .error (.unsupported "break or continue outside a loop")
        else .error (.unsupported s!"{m} is not a method")
end

/-- Call method `m` on an object whose state is `σ`, in the store model. -/
def runMethodStore (p : Program) (fuel : Nat) (m : String) (σ : JSValue) (args : List JSValue) :
    Except Fault (JSValue × JSValue) :=
  if p.scoped then sCallState p fuel m σ args else .error (.unsupported "program fails the static scoping check")

end V2

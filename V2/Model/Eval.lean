import V2.Model.Syntax

/-!
# The trusted model: a value semantics of the subset

A big-step evaluator over plain JavaScript values, with no heap. In this subset
nothing is mutated in place and nothing compares objects by identity, so
JavaScript's reference semantics and this value semantics agree.

Evaluation is bounded by fuel, which limits nesting depth (expressions, statement
lists and calls). Every definition is structurally recursive on the fuel, so the
evaluator runs in compiled Lean (for differential tests) and reduces in the kernel.

The model faults (`typeError`) wherever JavaScript would coerce operands of
unexpected types: well-typed programs never reach those cases, and the model
makes no claim about them.
-/

namespace V2

inductive JSValue where
  | undefined
  | bool (b : Bool)
  | bigint (n : Int)
  | string (s : JSString)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Fault where
  | timeout
  | typeError (message : String)
  | referenceError (name : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Bindings in scope, innermost first. Lookup finds the innermost binding. -/
abbrev Env := List (String × JSValue)

inductive Outcome where
  /-- Ran to the end of the list; the environment includes its declarations. -/
  | normal (env : Env)
  | returned (value : JSValue)
  deriving Repr, BEq, Inhabited

/-! ## Primitive operations, shared with the denotation -/

/-- `a < b` on strings: lexicographic order of UTF-16 code units. -/
def strLt : JSString → JSString → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else strLt as bs

def strLe (a b : JSString) : Bool := !strLt b a

def Lit.value : Lit → JSValue
  | .bool b => .bool b
  | .bigint n => .bigint n
  | .string s => .string s

def unary : UnOp → JSValue → Except Fault JSValue
  | .not, .bool b => .ok (.bool !b)
  | .neg, .bigint n => .ok (.bigint (-n))
  | _, _ => .error (.typeError "unary operand")

/-- Strict equality of primitives: by value. -/
def strictEq : JSValue → JSValue → Except Fault Bool
  | .bool a, .bool b => .ok (a == b)
  | .bigint a, .bigint b => .ok (a == b)
  | .string a, .string b => .ok (a == b)
  | .undefined, .undefined => .ok true
  | _, _ => .error (.typeError "strict equality operands")

/-- Non-short-circuiting binary operators. -/
def binary : BinOp → JSValue → JSValue → Except Fault JSValue
  | .add, .bigint a, .bigint b => .ok (.bigint (a + b))
  | .add, .string a, .string b => .ok (.string (a ++ b))
  | .sub, .bigint a, .bigint b => .ok (.bigint (a - b))
  | .mul, .bigint a, .bigint b => .ok (.bigint (a * b))
  | .eq, a, b => return .bool (← strictEq a b)
  | .ne, a, b => return .bool !(← strictEq a b)
  | .lt, .bigint a, .bigint b => .ok (.bool (decide (a < b)))
  | .le, .bigint a, .bigint b => .ok (.bool (decide (a ≤ b)))
  | .gt, .bigint a, .bigint b => .ok (.bool (decide (b < a)))
  | .ge, .bigint a, .bigint b => .ok (.bool (decide (b ≤ a)))
  | .lt, .string a, .string b => .ok (.bool (strLt a b))
  | .le, .string a, .string b => .ok (.bool (strLe a b))
  | .gt, .string a, .string b => .ok (.bool (strLt b a))
  | .ge, .string a, .string b => .ok (.bool (strLe b a))
  | _, _, _ => .error (.typeError "binary operands")

/-- Leaving a block discards its declarations: keep the bindings that were in scope
when it started (declarations are added at the front). -/
def restore (outer inner : Env) : Env := inner.drop (inner.length - outer.length)

/-! ## Evaluation -/

mutual
  def evalExpr (p : Program) : Nat → Env → Expr → Except Fault JSValue
    | 0, _, _ => .error .timeout
    | _ + 1, _, .lit l => .ok l.value
    | _ + 1, env, .var x => match env.lookup x with
      | some v => .ok v
      | none => .error (.referenceError x)
    | n + 1, env, .unary op e => do unary op (← evalExpr p n env e)
    | n + 1, env, .binary .and a b => do
      match ← evalExpr p n env a with
      | .bool false => .ok (.bool false)
      | .bool true => evalExpr p n env b
      | _ => .error (.typeError "&& operand")
    | n + 1, env, .binary .or a b => do
      match ← evalExpr p n env a with
      | .bool true => .ok (.bool true)
      | .bool false => evalExpr p n env b
      | _ => .error (.typeError "|| operand")
    | n + 1, env, .binary op a b => do
      let x ← evalExpr p n env a
      let y ← evalExpr p n env b
      binary op x y
    | n + 1, env, .cond c a b => do
      match ← evalExpr p n env c with
      | .bool true => evalExpr p n env a
      | .bool false => evalExpr p n env b
      | _ => .error (.typeError "condition")
    | n + 1, env, .call f args => do
      let vs ← evalArgs p n env args
      call p n f vs

  def evalArgs (p : Program) : Nat → Env → List Expr → Except Fault (List JSValue)
    | 0, _, _ => .error .timeout
    | _ + 1, _, [] => .ok []
    | n + 1, env, e :: es => do
      let v ← evalExpr p n env e
      let vs ← evalArgs p n env es
      return v :: vs

  /-- Calls bind the parameters in a fresh environment; falling off the end of the
  body returns `undefined`. -/
  def call (p : Program) : Nat → String → List JSValue → Except Fault JSValue
    | 0, _, _ => .error .timeout
    | n + 1, f, vs => match p.find? (·.name == f) with
      | none => .error (.referenceError f)
      | some fn =>
        if fn.params.length != vs.length then .error (.typeError "argument count") else do
        match ← execStmts p n (fn.params.zip vs) fn.body with
        | .returned v => .ok v
        | .normal _ => .ok .undefined

  def execStmts (p : Program) : Nat → Env → List Stmt → Except Fault Outcome
    | 0, _, _ => .error .timeout
    | _ + 1, env, [] => .ok (.normal env)
    | n + 1, env, s :: rest => do
      match ← execStmt p n env s with
      | .returned v => .ok (.returned v)
      | .normal env' => execStmts p n env' rest

  def execStmt (p : Program) : Nat → Env → Stmt → Except Fault Outcome
    | 0, _, _ => .error .timeout
    | n + 1, env, .const x e => do
      let v ← evalExpr p n env e
      return .normal ((x, v) :: env)
    | n + 1, env, .ret e => do
      return .returned (← evalExpr p n env e)
    | n + 1, env, .ite c yes no => do
      let branch ← match ← evalExpr p n env c with
        | .bool true => .ok yes
        | .bool false => .ok no
        | _ => .error (.typeError "condition")
      match ← execStmts p n env branch with
      | .returned v => .ok (.returned v)
      | .normal env' => .ok (.normal (restore env env'))
end

/-! ## Scoping

JavaScript resolves names lexically: a block's `const` declarations are in scope
for the whole block (reading one before its declaration throws), and a local
shadows a function of the same name. The evaluator resolves variables in the
environment and functions in the program, which agrees with JavaScript exactly
when no declaration reuses a name in scope or a function's name. `run` checks
this first; then reading a name before its declaration is a `referenceError`
in both. -/

def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

mutual
  /-- Declarations in `ss`, run with `scope` bound, reuse no name in scope and no
  function name. -/
  def stmtsScoped (fns : List String) : List String → List Stmt → Bool
    | _, [] => true
    | scope, s :: rest => stmtScoped fns scope s && stmtsScoped fns (s.declares ++ scope) rest

  def stmtScoped (fns : List String) : List String → Stmt → Bool
    | scope, .const x _ => !scope.contains x && !fns.contains x
    | _, .ret _ => true
    | scope, .ite _ yes no => stmtsScoped fns scope yes && stmtsScoped fns scope no
end

def Program.scoped (p : Program) : Bool :=
  let fns := p.map (·.name)
  distinct fns && p.all fun fn =>
    distinct fn.params && fn.params.all (!fns.contains ·) && stmtsScoped fns fn.params fn.body

/-- Call `f` in `p`, refusing programs whose scoping the evaluator does not model. -/
def run (p : Program) (fuel : Nat) (f : String) (args : List JSValue) : Except Fault JSValue :=
  if p.scoped then call p fuel f args else .error (.typeError "shadowed declaration")

/-- `f` eventually stabilises at `a`: every budget from some point on gives `a`. -/
def Converges (f : Nat → α) (a : α) : Prop := ∃ n, ∀ m, n ≤ m → f m = a

end V2

import Ariadne.Shallow.Core

namespace Ariadne.Shallow
open Core

def Denote.unary : Unary a b → a.denote → b.denote
  | .not, a => !a
  | .intNeg, a => -a
  | .numNeg, a => -a
  | .isSome, a => a.isSome

def Denote.binary : Binary a b c → a.denote → b.denote → c.denote
  | .intAdd, a, b => a + b
  | .intSub, a, b => a - b
  | .intMul, a, b => a * b
  | .intEq, a, b => a == b
  | .intLt, a, b => decide (a < b)
  | .intLe, a, b => decide (a ≤ b)
  | .numAdd, a, b => a + b
  | .numSub, a, b => a - b
  | .numMul, a, b => a * b
  | .numDiv, a, b => a / b
  | .numMod, a, b => numberRemainder a b
  | .numEq, a, b => a == b
  | .numLt, a, b => decide (a < b)
  | .numLe, a, b => decide (a ≤ b)
  | .strAppend, a, b => a ++ b
  | .strEq, a, b => a == b
  | .strLt, a, b => compare a b == .lt
  | .strLe, a, b => compare a b != .gt
  | .boolEq, a, b => a == b
  | .and, a, b => a && b
  | .or, a, b => a || b

/-- Structural interpretation into native Lean values. -/
def Denote.term : Term Γ t → Core.Env Γ → t.denote
  | .var v, env => v.get env
  | .unit, _ => ()
  | .bool b, _ => b
  | .int n, _ => n
  | .number m e, _ => Float.Model.ofScientific m e
  | .string s, _ => s
  | .unary op a, env => unary op (term a env)
  | .binary op a b, env => binary op (term a env) (term b env)
  | .let_ _ a b, env => term b (term a env, env)
  | .ite c a b, env => if term c env then term a env else term b env
  | .none, _ => none
  | .some a, env => some (term a env)
  | .optionCase a b c, env => (term a env).elim (term b env) (fun x => term c (x, env))
  | .nil, _ => []
  | .cons a b, env => term a env :: term b env
  | .pair a b, env => (term a env, term b env)
  | .fst a, env => (term a env).1
  | .snd a, env => (term a env).2
  | .lam _ body, env => fun x => term body (x, env)
  | .app f a, env => term f env (term a env)
  | .closed body, _ => term body ()

def Denote.function (f : Core.Function) : Core.Env f.params → f.result.denote := term f.body

end Ariadne.Shallow

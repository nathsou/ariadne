import V2.Typed.Syntax

/-!
# Denotation

Expressions denote functions of the environment tuple. Statement lists denote in
continuation-passing style: `ss.denote fs k ρ` is the function's result when the
list runs in `ρ` and `k` gives the result of what follows it. Early `return`
discards `k`. This keeps the denotation of `if (c) return a; …` definitionally
`if c then a else …`, so printed definitions are checked by `rfl`.
-/

namespace V2

/-- Strict equality on denoted primitives. -/
def Ty.beq : (τ : Ty) → τ.denote → τ.denote → Bool
  | .bool, a, b => a == b
  | .int, a, b => a == b
  | .string, a, b => a == b

mutual
  def TExpr.denote (fs : Φ.denote) : TExpr Φ Γ τ → Γ.denote → τ.denote
    | .bool b, _ => b
    | .int n, _ => n
    | .str s, _ => s
    | .var v, ρ => v.get ρ
    | .not e, ρ => !e.denote fs ρ
    | .neg e, ρ => -e.denote fs ρ
    | .add a b, ρ => a.denote fs ρ + b.denote fs ρ
    | .sub a b, ρ => a.denote fs ρ - b.denote fs ρ
    | .mul a b, ρ => a.denote fs ρ * b.denote fs ρ
    | .concat a b, ρ => a.denote fs ρ ++ b.denote fs ρ
    | .eq a b, ρ => Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)
    | .ne a b, ρ => !Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)
    | .lt a b, ρ => decide (a.denote fs ρ < b.denote fs ρ)
    | .le a b, ρ => decide (a.denote fs ρ ≤ b.denote fs ρ)
    | .gt a b, ρ => decide (b.denote fs ρ < a.denote fs ρ)
    | .ge a b, ρ => decide (b.denote fs ρ ≤ a.denote fs ρ)
    | .slt a b, ρ => strLt (a.denote fs ρ) (b.denote fs ρ)
    | .sle a b, ρ => strLe (a.denote fs ρ) (b.denote fs ρ)
    | .sgt a b, ρ => strLt (b.denote fs ρ) (a.denote fs ρ)
    | .sge a b, ρ => strLe (b.denote fs ρ) (a.denote fs ρ)
    | .and a b, ρ => a.denote fs ρ && b.denote fs ρ
    | .or a b, ρ => a.denote fs ρ || b.denote fs ρ
    | .cond c a b, ρ => if c.denote fs ρ then a.denote fs ρ else b.denote fs ρ
    | .call fn args, ρ => fn.get fs (args.denote fs ρ)

  def TArgs.denote (fs : Φ.denote) : TArgs Φ Γ ps → Γ.denote → ps.denote
    | .nil, _ => ()
    | .cons e rest, ρ => (e.denote fs ρ, rest.denote fs ρ)
end

def TStmts.denote (fs : Φ.denote) : TStmts Φ Γ τ → (Γ.denote → τ.denote) → Γ.denote → τ.denote
  | .nil, k, ρ => k ρ
  | .const _ e rest, k, ρ => rest.denote fs (fun ρ' => k ρ'.2) (e.denote fs ρ, ρ)
  | .ret e _, _, ρ => e.denote fs ρ
  | .ite c yes no rest, k, ρ =>
    if c.denote fs ρ then yes.denote fs (rest.denote fs k) ρ else no.denote fs (rest.denote fs k) ρ

/-- A function body; falling off the end (excluded by `TProgram.WF`) gives the default. -/
def TStmts.denoteFn (fs : Φ.denote) (body : TStmts Φ Γ τ) : Γ.denote → τ.denote :=
  body.denote fs (fun _ => τ.default)

/-- Each function denotes in terms of the ones declared before it. -/
def TProgram.denote : TProgram Φ → Φ.denote
  | .nil => ()
  | .cons _ body rest => (body.denoteFn rest.denote, rest.denote)

/-- Distinct function names, and every body returns on every path. -/
def TProgram.WF (P : TProgram Φ) : Prop := P.names.Nodup ∧ P.returns = true

instance (P : TProgram Φ) : Decidable P.WF := inferInstanceAs (Decidable (_ ∧ _))

end V2

import Ariadne.Kernel
import Ariadne.Check
import Ariadne.Semantics

namespace Ariadne

theorem frontend_of_parse {source : String} {program : Program}
    (parsed : parse source = .ok program) (checked : Check.program program = .ok ()) :
    frontend source = .ok program := by
  unfold frontend
  rw [parsed]
  change (Check.program program).map (fun _ => program) = .ok program
  rw [checked]
  rfl

/-- A kernel-checkable binding between exact source text and its checked syntax tree. -/
structure Certificate (source : String) where
  program : Program
  checked : frontend source = .ok program

/-- The frontend is deterministic: a certificate cannot substitute a different AST. -/
theorem Certificate.unique {source : String} (a b : Certificate source) :
    a.program = b.program := by
  have h := a.checked.symm.trans b.checked
  exact Except.ok.inj h

def SourceReturns (source name : String) (args : List Value) (value : Value) : Prop :=
  ∃ program, frontend source = .ok program ∧ Returns program name args value

theorem Certificate.transfer {source : String} (c : Certificate source)
    {name : String} {args : List Value} {value : Value}
    (h : Returns c.program name args value) : SourceReturns source name args value :=
  ⟨c.program, c.checked, h⟩

theorem Certificate.transfer_at {source : String} (c : Certificate source)
    {name : String} {args : List Value} {value : Value} {fuel : Nat}
    (h : run c.program name fuel args = .ok value) : SourceReturns source name args value :=
  c.transfer ⟨fuel, h⟩

/-- Properties of every modeled return transfer back to the source-bound program. -/
theorem Certificate.transfer_property {source : String} (c : Certificate source)
    {name : String} {args : List Value} {post : Value → Prop}
    (h : ∀ v, Returns c.program name args v → post v) :
    ∀ v, SourceReturns source name args v → post v := by
  intro v ⟨p, hp, hv⟩
  have eq : p = c.program := Except.ok.inj (hp.symm.trans c.checked)
  subst p
  exact h v hv

end Ariadne

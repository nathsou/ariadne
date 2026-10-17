import Ariadne.Typed.Ty
import Lean

/-! Proof-facing safety specifications. The raw Boolean condition is retained for the
structural certificate. `safety_spec f.safe => f.safe_iff` adds a kernel-checked
equivalence to a simplified proposition, usable with `rw [f.safe_iff]`.
It does not unfold callees or loop combinators. -/
namespace Ariadne

theorem inRange_zero : inRange 0 = true := by decide
theorem inRange_one : inRange 1 = true := by decide
theorem inRange_two : inRange 2 = true := by decide

open Lean Meta Elab Command in
elab "safety_spec " source:ident " => " destination:ident : command => do
  let name := (← getCurrNamespace) ++ destination.getId
  liftTermElabM do
    let src ← realizeGlobalConstNoOverloadWithInfo source
    let info ← getConstInfoDefn src
    lambdaTelescope info.value fun xs body => do
      unless ← isDefEq (← inferType body) (mkConst ``Bool) do
        throwError "safety_spec expects a Boolean-valued definition"
      let lhs ← mkEq (mkAppN (mkConst src (info.levelParams.map Level.param)) xs) (mkConst ``Bool.true)
      let unfolded ← mkEq body (mkConst ``Bool.true)
      let mut theorems : SimpTheorems := {}
      for lemma in [``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true',
          ``Bool.false_eq_true, ``eq_self, ``and_true, ``true_and, ``and_self,
          ``or_true, ``true_or, ``or_false, ``false_or, ``or_self,
          ``decide_eq_true_eq, ``inRange_zero, ``inRange_one, ``inRange_two] do
        theorems ← theorems.addConst lemma
      let context ← Simp.mkContext (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
      let (result, _) ← simp unfolded context #[← Simp.getSimprocs]
      let proof ← mkAppM ``Iff.of_eq #[← result.getProof' unfolded]
      let theoremType ← mkForallFVars xs (← mkAppM ``Iff #[lhs, result.expr])
      let theoremProof ← mkLambdaFVars xs proof
      addDecl <| Declaration.thmDecl {
        name := name
        levelParams := info.levelParams
        type := theoremType
        value := theoremProof
      }

end Ariadne

import Ariadne.Shallow.Safety
import Ariadne.Shallow.Adequacy.Scalar

namespace Ariadne.Shallow.Safety
open Core
open Adequacy (Scalar)

/-- Scalar safety values have the same data representation as denotation. -/
def scalarValue {interp : Named.Interp} : (scalar : Scalar t) → Model t interp → t.denote interp
  | .unit, value => value
  | .bool, value => value
  | .int, value => value
  | .int53, value => value
  | .number, value => value
  | .string, value => value

def ScalarEnvironment {interp : Named.Interp} (model : Environment Γ interp) (native : Core.Env Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t) (scalar : Scalar t), scalarValue scalar (getVariable v model) = v.get native

theorem ScalarEnvironment.cons {interp : Named.Interp} {model : Environment Γ interp} {native : Core.Env Γ interp}
    (related : ScalarEnvironment model native) (scalar : Scalar t) (value : Model t interp) (expected : t.denote interp)
    (equal : scalarValue scalar value = expected) : ScalarEnvironment (Γ := t :: Γ) (interp := interp) (value, model) (expected, native) := by
  intro u v repr
  cases v with
  | here => cases scalar <;> cases repr <;> exact equal
  | there v => exact related v repr

theorem scalar_unary_value (sa : Scalar a) (sb : Scalar b) (op : Unary a b)
    (interp : Named.Interp) (value : Model a interp) :
    scalarValue sb (unary op value) = Denote.unary op (scalarValue sa value) := by
  cases op <;> cases sa <;> cases sb <;> rfl

theorem scalar_binary_value (sa : Scalar a) (sb : Scalar b) (sc : Scalar c) (op : Binary a b c)
    (interp : Named.Interp) (left : Model a interp) (right : Model b interp) :
    scalarValue sc (binary op left right) = Denote.binary op (scalarValue sa left) (scalarValue sb right) := by
  cases op <;> cases sa <;> cases sb <;> cases sc <;> rfl

/-- Typed evidence that a Core expression only computes scalar values. This
includes arithmetic guard expressions, without presuming that their guards hold. -/
inductive ScalarTerm : {Γ : List Core.Ty} → {t : Core.Ty} → Scalar t → Term Γ t → Prop where
  | var (scalar : Scalar t) (v : Var Γ t) : ScalarTerm scalar (.var v)
  | unit : ScalarTerm .unit (.unit : Term Γ .unit)
  | bool (value : Bool) : ScalarTerm .bool (.bool value : Term Γ .bool)
  | int (value : Int) : ScalarTerm .int (.int value : Term Γ .int)
  | number (mantissa : Nat) (exponent : Int) : ScalarTerm .number (.number mantissa exponent : Term Γ .number)
  | string (value : JSString) : ScalarTerm .string (.string value : Term Γ .string)
  | unary {sa : Scalar a} {sb : Scalar b} (op : Unary a b) {value : Term Γ a}
      (input : ScalarTerm sa value) : ScalarTerm sb (.unary op value)
  | binary {sa : Scalar a} {sb : Scalar b} {sc : Scalar c} (op : Binary a b c) {a : Term Γ a} {b : Term Γ b}
      (left : ScalarTerm sa a) (right : ScalarTerm sb b) : ScalarTerm sc (.binary op a b)
  | let_ {sa : Scalar a} {sb : Scalar b} (name : String) {value : Term Γ a} {body : Term (a :: Γ) b}
      (input : ScalarTerm sa value) (next : ScalarTerm sb body) : ScalarTerm sb (.let_ name value body)
  | ite {scalar : Scalar t} {condition : Term Γ .bool} {yes no : Term Γ t}
      (test : ScalarTerm .bool condition) (yesBody : ScalarTerm scalar yes) (noBody : ScalarTerm scalar no) :
      ScalarTerm scalar (.ite condition yes no)
  | closed {scalar : Scalar t} {body : Term [] t} (input : ScalarTerm scalar body) :
      ScalarTerm scalar (Term.closed (Γ := Γ) body)

/-- Collecting scalar guards changes no computed value, even if a guard fails. -/
theorem ScalarTerm.value {interp : Named.Interp} {scalar : Scalar t} {body : Term Γ t}
    (input : ScalarTerm scalar body) (model : Environment Γ interp) (native : Core.Env Γ interp)
    (related : ScalarEnvironment model native) :
    scalarValue scalar (term body model).1 = Denote.term body native := by
  induction input with
  | var scalar v => exact related v scalar
  | unit => rfl
  | bool value => rfl
  | int value => rfl
  | number mantissa exponent => rfl
  | string value => rfl
  | unary op input ih =>
    change scalarValue _ (Safety.unary op (term _ model).1) = _
    rw [scalar_unary_value]
    exact congrArg (Denote.unary op) (ih model native related)
  | binary op left right ihl ihr =>
    change scalarValue _ (Safety.binary op (term _ model).1 (term _ model).1) = _
    rw [scalar_binary_value, ihl model native related, ihr model native related]
    rfl
  | let_ name input next ihv ihb =>
    apply ihb
    exact ScalarEnvironment.cons related _ _ _ (ihv model native related)
  | @ite t Γ scalar condition yes no test yesBody noBody ihc ihy ihn =>
    have testValue : (term condition model).1 = Denote.term condition native := ihc model native related
    cases value : Denote.term condition native
    · simpa only [term, testValue, Denote.term, value, Bool.false_eq_true, ↓reduceIte] using ihn model native related
    · simpa only [term, testValue, Denote.term, value, ↓reduceIte] using ihy model native related
  | closed input ih =>
    exact ih () () (by intro t v scalar; cases v)

theorem scalar_lift_environment {interp : Named.Interp} (types : List Core.Ty)
    (data : types.all dataType = true) (env : Core.Env types interp) :
    ScalarEnvironment (liftEnvironment types data env) env := by
  intro t v scalar
  induction v with
  | here => cases scalar <;> rfl
  | @there types t other v ih =>
    have h : dataType other = true ∧ types.all dataType = true := by simpa using data
    exact ih h.2 env.2 scalar

theorem ScalarTerm.lift_value {interp : Named.Interp} {scalar : Scalar t} {body : Term Γ t}
    (input : ScalarTerm scalar body) (data : Γ.all dataType = true) (env : Core.Env Γ interp) :
    scalarValue scalar (term body (liftEnvironment Γ data env)).1 = Denote.term body env :=
  input.value _ _ (scalar_lift_environment Γ data env)

/-- A visited Core guard is true in the native denotation whenever the actual
safety interpreter accepts it. Subexpression guards remain available separately. -/
theorem guard_holds {interp : Named.Interp} {condition : Term Γ .bool} {body : Term Γ t}
    (input : ScalarTerm .bool condition) (model : Environment Γ interp) (native : Core.Env Γ interp)
    (related : ScalarEnvironment model native)
    (safe : (term (.binary .guard condition body) model).2 = true) :
    Denote.term condition native = true ∧ (term condition model).2 = true ∧ (term body model).2 = true := by
  have value : (term condition model).1 = Denote.term condition native := input.value model native related
  simp only [term, binarySafe, Bool.and_eq_true] at safe
  exact ⟨value.symm.trans safe.2, safe.1.1, safe.1.2⟩

end Ariadne.Shallow.Safety

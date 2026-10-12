import Ariadne.CallConvergence
import Ariadne.Shallow.Safety.Scalar
import Ariadne.Shallow.Prelude.Int53Exact
import Ariadne.Shallow.Adequacy.Function

namespace Ariadne.Shallow.Adequacy
open Core

theorem ScalarExpr.scalarCore {names : Names Γ} {scalar : Scalar t} {source : Expr} {body : Term Γ t}
    (input : ScalarExpr names scalar source body) : Safety.ScalarTerm scalar body := by
  induction input with
  | unit span => exact .unit
  | bool b span => exact .bool b
  | int n span => exact .int n
  | number m e span => exact .number m e
  | string s span => exact .string s
  | var scalar v span visible => exact .var scalar v
  | unary rule input span ih => exact .unary _ ih
  | notIte input span ih => exact .ite ih (.bool false) (.bool true)
  | boolIte input ih => exact .ite ih (.bool true) (.bool false)
  | binary rule left right span ihl ihr => exact .binary _ ihl ihr
  | conditional input yes no span ihc ihy ihn => exact .ite ihc ihy ihn
  | and left right span ihl ihr => exact .ite ihl ihr (.bool false)
  | or left right span ihl ihr => exact .ite ihl (.bool true) ihr

def guardedInteger (value : Term Γ .int) (number : Term Γ .number) : Term Γ .int53 :=
  let result := Term.unary .intToInt53 value
  .binary .guard (.binary .numBitsEq number (.unary .int53ToNumber result)) result

inductive Int53Comparison : String → Binary .int .int .bool → Prop where
  | eq : Int53Comparison "===" .intEq
  | lt : Int53Comparison "<" .intLt
  | le : Int53Comparison "<=" .intLe

theorem Int53Comparison.strict {source : String} {op : Binary .int .int .bool}
    (rule : Int53Comparison source op) : source ≠ "&&" ∧ source ≠ "||" ∧ source ≠ "??" := by
  cases rule <;> decide

theorem Int53Comparison.correct {source : String} {op : Binary .int .int .bool}
    (rule : Int53Comparison source op) (interp : Named.Interp) (a b : Int)
    (ha : Int53.InRange a) (hb : Int53.InRange b) :
    Ariadne.binary source (.number (Float.Model.ofInt a)) (.number (Float.Model.ofInt b)) =
      .ok (.boolean (Denote.binary (interp := interp) op a b)) := by
  cases rule with
  | eq =>
    change Except.ok (Value.boolean (Float.Model.ofInt a == Float.Model.ofInt b)) = _
    rw [Int53.beq_ofInt a b ha hb]
    rfl
  | lt =>
    change Except.ok (Value.boolean (decide (Float.Model.ofInt a < Float.Model.ofInt b))) = _
    simp only [Int53.lt_ofInt a b ha hb]
    rfl
  | le =>
    change Except.ok (Value.boolean (decide (Float.Model.ofInt a ≤ Float.Model.ofInt b))) = _
    simp only [Int53.le_ofInt a b ha hb]
    rfl

/-- Builtin resolution is checked against the actual caller frame and program. -/
structure MathFree (program : Program) (state : State) : Prop where
  unbound : state.env.any (fun p => p.1 == "Math") = false
  abs : program.functions.find? (fun f => f.name == "Math.abs") = none
  floor : program.functions.find? (fun f => f.name == "Math.floor") = none
  trunc : program.functions.find? (fun f => f.name == "Math.trunc") = none

inductive MathUnary : String → Unary .number .number → Prop where
  | abs : MathUnary "abs" .numAbs
  | floor : MathUnary "floor" .numFloor
  | trunc : MathUnary "trunc" .numTrunc

theorem MathUnary.correct {method : String} {op : Unary .number .number}
    (rule : MathUnary method op) (interp : Named.Interp) (value : Float.Model) :
    invokeScalar ("Math." ++ method) [.number value] = .ok (.number (Denote.unary (interp := interp) op value)) := by
  cases rule <;> rfl

theorem MathUnary.absent {method : String} {op : Unary .number .number}
    (rule : MathUnary method op) {program : Program} {state : State} (free : MathFree program state) :
    program.functions.find? (fun f => f.name == "Math." ++ method) = none := by
  cases rule
  · exact free.abs
  · exact free.floor
  · exact free.trunc

/-- Scalar expression correspondence that consumes the emitted safety guards.
The integer wrapper checks primitive bit equality, including the sign of zero. -/
inductive GuardedScalarExpr {Γ : List Core.Ty} (names : Names Γ) :
    {t : Core.Ty} → Scalar t → Expr → Term Γ t → Prop where
  | total {scalar : Scalar t} {source : Expr} {body : Term Γ t}
      (input : ScalarExpr names scalar source body) : GuardedScalarExpr names scalar source body
  | widen {source : Expr} {body : Term Γ .int53}
      (input : GuardedScalarExpr names .int53 source body) :
      GuardedScalarExpr names .number source (.unary .int53ToNumber body)
  | integer {source : Expr} {value : Term Γ .int} {number : Term Γ .number}
      (native : Safety.ScalarTerm .int value) (input : GuardedScalarExpr names .number source number) :
      GuardedScalarExpr names .int53 source (guardedInteger value number)
  | unary {sa : Scalar a} {sb : Scalar b} {source : String} {op : Unary a b} {arg : Expr} {term : Term Γ a}
      (rule : UnaryRule sa sb source op) (input : GuardedScalarExpr names sa arg term) (span : Span) :
      GuardedScalarExpr names sb (.unary source arg span) (.unary op term)
  | binary {sa : Scalar a} {sb : Scalar b} {sc : Scalar c} {source : String} {op : Binary a b c}
      {left right : Expr} {a : Term Γ a} {b : Term Γ b}
      (rule : BinaryRule sa sb sc source op)
      (lhs : GuardedScalarExpr names sa left a) (rhs : GuardedScalarExpr names sb right b) (span : Span) :
      GuardedScalarExpr names sc (.binary source left right span) (.binary op a b)
  | compare {source : String} {op : Binary .int .int .bool}
      {left right : Expr} {a b : Term Γ .int53} (rule : Int53Comparison source op)
      (lhs : GuardedScalarExpr names .int53 left a) (rhs : GuardedScalarExpr names .int53 right b) (span : Span) :
      GuardedScalarExpr names .bool (.binary source left right span)
        (.binary op (.unary .int53ToInt a) (.unary .int53ToInt b))
  | math {method : String} {op : Unary .number .number} {arg : Expr} {term : Term Γ .number}
      (rule : MathUnary method op) (input : GuardedScalarExpr names .number arg term)
      (nameSpan memberSpan callSpan : Span) :
      GuardedScalarExpr names .number (.call (.member (.var "Math" nameSpan) method memberSpan) [arg] callSpan)
        (.unary op term)
  | conditional {scalar : Scalar t} {condition yes no : Expr} {test : Term Γ .bool} {a b : Term Γ t}
      (input : GuardedScalarExpr names .bool condition test)
      (yesBody : GuardedScalarExpr names scalar yes a) (noBody : GuardedScalarExpr names scalar no b) (span : Span) :
      GuardedScalarExpr names scalar (.conditional condition yes no span) (.ite test a b)

private theorem integer_condition_core {value : Term Γ .int} {number : Term Γ .number}
    (native : Safety.ScalarTerm .int value) (input : Safety.ScalarTerm .number number) :
    Safety.ScalarTerm .bool (.binary .numBitsEq number (.unary .int53ToNumber (.unary .intToInt53 value))) := by
  have result : Safety.ScalarTerm .int53 (.unary .intToInt53 value) := .unary .intToInt53 native
  have widened : Safety.ScalarTerm .number (.unary .int53ToNumber (.unary .intToInt53 value)) := .unary .int53ToNumber result
  exact .binary .numBitsEq input widened

theorem GuardedScalarExpr.scalarCore {names : Names Γ} {scalar : Scalar t} {source : Expr} {body : Term Γ t}
    (input : GuardedScalarExpr names scalar source body) : Safety.ScalarTerm scalar body := by
  induction input with
  | total input => exact input.scalarCore
  | widen input ih => exact .unary .int53ToNumber ih
  | integer native input ih =>
    exact .binary .guard (integer_condition_core native ih) (.unary (sb := .int53) .intToInt53 native)
  | unary rule input span ih => exact .unary _ ih
  | math rule input nameSpan memberSpan callSpan ih => exact .unary _ ih
  | binary rule left right span ihl ihr => exact .binary _ ihl ihr
  | compare rule left right span ihl ihr =>
    exact .binary _ (.unary (sb := .int) .int53ToInt ihl) (.unary (sb := .int) .int53ToInt ihr)
  | conditional input yes no span ihc ihy ihn => exact .ite ihc ihy ihn

private theorem unary_parts {interp : Named.Interp} {op : Unary a b} {input : Term Γ a} {model : Safety.Environment Γ interp}
    (safe : (Safety.term (.unary op input) model).2 = true) :
    (Safety.term input model).2 = true ∧ Safety.unarySafe op (Safety.term input model).1 = true := by
  simpa only [Safety.term, Bool.and_eq_true] using safe

private theorem binary_parts {interp : Named.Interp} {op : Binary a b c} {left : Term Γ a} {right : Term Γ b}
    {model : Safety.Environment Γ interp} (safe : (Safety.term (.binary op left right) model).2 = true) :
    ((Safety.term left model).2 = true ∧ (Safety.term right model).2 = true) ∧
      Safety.binarySafe op (Safety.term left model).1 (Safety.term right model).1 = true := by
  simpa only [Safety.term, Bool.and_eq_true] using safe

/-- Fundamental scalar guard lemma in the original evaluator. Safety is the
actual Core guard interpreter, never a premise asserting source execution. -/
theorem GuardedScalarExpr.sound {names : Names Γ} {scalar : Scalar t} {source : Expr} {body : Term Γ t}
    (input : GuardedScalarExpr names scalar source body) (program : Program) (interp : Named.Interp)
    (state : State) (native : Core.Env Γ interp) (model : Safety.Environment Γ interp)
    (environment : Environment names state native) (values : Safety.ScalarEnvironment model native)
    (free : MathFree program state)
    (safe : (Safety.term body model).2 = true) :
    Evaluates program state source (scalar.encode (Denote.term body native)) state := by
  induction input with
  | total input => exact input.sound program interp state native environment
  | widen input ih => exact ih (unary_parts safe).1
  | @integer source value number core input ih =>
    have condition := Safety.guard_holds
      (integer_condition_core core input.scalarCore)
      model native values safe
    have sourceSafe := (binary_parts condition.2.1).1.1
    have exactBits : Int53.exact (Denote.term number native) (Denote.term value native) = true := condition.1
    have equal := (Int53.exact_iff _ _).mp exactBits
    have evaluated := ih sourceSafe
    change Evaluates program state source (.number (Denote.term number native)) state at evaluated
    change Evaluates program state source (.number (Float.Model.ofInt (Denote.term value native))) state
    simpa only [equal] using evaluated
  | unary rule input span ih =>
    exact (ih (unary_parts safe).1).unary _ span (rule.correct interp _)
  | binary rule left right span ihl ihr =>
    exact (ihl (binary_parts safe).1.1).binary (ihr (binary_parts safe).1.2) _ span rule.strict (rule.correct interp _ _)
  | @math method op arg term rule input nameSpan memberSpan callSpan ih =>
    have receiver := Evaluates.global program state "Math" free.unbound (by decide) nameSpan
    have callee := receiver.member method memberSpan (by rfl)
    have arguments := (EvaluatesArgs.nil program state).cons (ih (unary_parts safe).1)
    have invoked := Invokes.scalar program state ("Math." ++ method) [_] _ (rule.absent free) (rule.correct interp (Denote.term term native))
    exact callee.call arguments invoked callSpan
  | @compare source op left right a b rule lhs rhs span ihl ihr =>
    have parts := binary_parts safe
    have leftSafe := unary_parts parts.1.1
    have rightSafe := unary_parts parts.1.2
    have leftValue : (Safety.term a model).1 = Denote.term a native := lhs.scalarCore.value model native values
    have rightValue : (Safety.term b model).1 = Denote.term b native := rhs.scalarCore.value model native values
    have leftRange : Int53.InRange (Denote.term a native) := by
      apply (Int53.inRange_iff _).mp
      simpa only [Safety.unarySafe, leftValue] using leftSafe.2
    have rightRange : Int53.InRange (Denote.term b native) := by
      apply (Int53.inRange_iff _).mp
      simpa only [Safety.unarySafe, rightValue] using rightSafe.2
    exact (ihl leftSafe.1).binary (ihr rightSafe.1) _ span rule.strict (rule.correct interp _ _ leftRange rightRange)
  | @conditional t scalar condition yes no test a b input yesBody noBody span ihc ihy ihn =>
    have testValue : (Safety.term test model).1 = Denote.term test native := input.scalarCore.value model native values
    have parts : (Safety.term test model).2 = true ∧
        (if Denote.term test native then Safety.term a model else Safety.term b model).2 = true := by
      simpa only [Safety.term, testValue, Bool.and_eq_true] using safe
    cases testResult : Denote.term test native
    · have branch := ihn (by simpa [testResult] using parts.2)
      have branch' : Evaluates program state
          (if (Scalar.bool.encode (Denote.term test native)).truthy then yes else no)
          (scalar.encode (Denote.term b native)) state := by
        simpa [Scalar.encode, Value.truthy, testResult] using branch
      simpa [Denote.term, testResult] using Evaluates.conditional (ihc parts.1) branch' span
    · have branch := ihy (by simpa [testResult] using parts.2)
      have branch' : Evaluates program state
          (if (Scalar.bool.encode (Denote.term test native)).truthy then yes else no)
          (scalar.encode (Denote.term a native)) state := by
        simpa [Scalar.encode, Value.truthy, testResult] using branch
      simpa [Denote.term, testResult] using Evaluates.conditional (ihc parts.1) branch' span

/-- Guarded transfer for a returned scalar expression. The safety premise is
exactly the existing interpreter applied to the actual Core body. -/
theorem guarded_scalar_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (names : Names Γ) (scalar : Scalar t) (body : Term Γ t)
    (expression : Expr) (returnSpan blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (sourceBody : function.body = .block [.return_ expression returnSpan] blockSpan)
    (translation : GuardedScalarExpr names scalar expression body)
    (interp : Named.Interp) (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : Environment names (bindArguments { heap } function.params args) env)
    (free : MathFree certificate.program (bindArguments { heap } function.params args))
    (data : Γ.all Safety.dataType = true)
    (safe : (Safety.term body (Safety.liftEnvironment Γ data env)).2 = true) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term body env)) := by
  apply certificate.transfer_from
  exact invoke_return lookup sourceBody
    (translation.sound certificate.program interp _ env _ inputs (Safety.scalar_lift_environment Γ data env) free safe)

end Ariadne.Shallow.Adequacy

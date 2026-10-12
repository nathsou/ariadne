import Ariadne.Shallow.Adequacy.GuardedScalar
import Ariadne.Shallow.Adequacy.Statements

namespace Ariadne.Shallow.Adequacy
open Core

theorem MathFree.declare {program : Program} {state : State} (free : MathFree program state)
    (name : String) (different : name ≠ "Math") (value : Value) : MathFree program (state.declare name value) := by
  refine ⟨?_, free.abs, free.floor, free.trunc⟩
  simpa [State.declare, State.alloc, different] using free.unbound

theorem MathFree.withHeap {program : Program} {state : State} (free : MathFree program state)
    (heap : Heap) : MathFree program {state with heap} :=
  ⟨free.unbound, free.abs, free.floor, free.trunc⟩

/-- Returned statement sequences related to the actual typed Core body. Local
bindings extend both environments; early returns discard the source suffix. -/
inductive GuardedStatements : {Γ : List Core.Ty} → Names Γ → {t : Core.Ty} → Scalar t →
    List Stmt → Term Γ t → Prop where
  | return_ {names : Names Γ} {scalar : Scalar t} {expression : Expr} {term : Term Γ t}
      (input : GuardedScalarExpr names scalar expression term) (span : Span) (rest : List Stmt) :
      GuardedStatements names scalar (.return_ expression span :: rest) term
  | let_ {names : Names Γ} {scalar : Scalar t} {repr : Scalar a} {expression : Expr}
      {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
      (name : String) (unshadow : name ≠ "Math") (input : GuardedScalarExpr names repr expression value)
      (next : GuardedStatements (names.cons name) scalar rest body)
      (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
      GuardedStatements names scalar (.let_ mutable name annotation expression span :: rest) (.let_ name value body)
  | assign {names : Names Γ} {scalar : Scalar t} {repr : Scalar a} {expression : Expr}
      {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
      (target : Var Γ a) (visible : names.visible target = true)
      (input : GuardedScalarExpr names repr expression value)
      (next : GuardedStatements (names.cons (names.get target)) scalar rest body)
      (targetSpan span : Span) :
      GuardedStatements names scalar (.assign (.var (names.get target) targetSpan) expression span :: rest)
        (.let_ (names.get target) value body)
  | block {names : Names Γ} {scalar : Scalar t} {statements : List Stmt} {term : Term Γ t}
      (body : GuardedStatements names scalar statements term) (span : Span) (rest : List Stmt) :
      GuardedStatements names scalar (.block statements span :: rest) term
  | emptyBlock {names : Names Γ} {scalar : Scalar t} {rest : List Stmt} {term : Term Γ t}
      (next : GuardedStatements names scalar rest term) (span : Span) :
      GuardedStatements names scalar (.block [] span :: rest) term
  | if_ {names : Names Γ} {scalar : Scalar t} {condition : Expr} {yes no : Stmt} {rest : List Stmt}
      {test : Term Γ .bool} {a b : Term Γ t}
      (input : GuardedScalarExpr names .bool condition test)
      (yesBody : GuardedStatements names scalar (yes :: rest) a)
      (noBody : GuardedStatements names scalar (no :: rest) b) (span : Span) :
      GuardedStatements names scalar (.if_ condition yes no span :: rest) (.ite test a b)

theorem GuardedStatements.sound {names : Names Γ} {scalar : Scalar t} {statements : List Stmt} {term : Term Γ t}
    (translation : GuardedStatements names scalar statements term) (program : Program) (interp : Named.Interp)
    (state : State) (env : Core.Env Γ interp) (model : Safety.Environment Γ interp)
    (related : Environment names state env) (bindings : state.ValidBindings)
    (values : Safety.ScalarEnvironment model env) (free : MathFree program state)
    (safe : (Safety.term term model).2 = true) :
    ∃ after, ExecutesBlock program state statements
      { control := .returned, value := scalar.encode (Denote.term term env), state := after } := by
  induction translation generalizing state with
  | return_ input span rest =>
    exact ⟨state, ExecutesBlock.stop (ExecutesStatement.return_
      (input.sound program interp state env model related values free safe) span) rest (by intro h; cases h)⟩
  | @let_ Γ t a names scalar repr expression value body rest name unshadow input next mutable annotation span ih =>
    have parts : (Safety.term value model).2 = true ∧
        (Safety.term body ((Safety.term value model).1, model)).2 = true := by
      simpa only [Safety.term, Bool.and_eq_true] using safe
    obtain ⟨after, executed⟩ := ih (state.declare name (repr.encode (Denote.term value env)))
      (Denote.term value env, env) ((Safety.term value model).1, model)
      (related.declare name repr _) (bindings.declare name _)
      (values.cons repr _ _ (input.scalarCore.value model env values)) (free.declare name unshadow _) parts.2
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.let_
      (input.sound program interp state env model related values free parts.1) mutable name annotation span) rfl executed⟩
  | @assign Γ t a names scalar repr expression value body rest target visible input next targetSpan span ih =>
    have parts : (Safety.term value model).2 = true ∧
        (Safety.term body ((Safety.term value model).1, model)).2 = true := by
      simpa only [Safety.term, Bool.and_eq_true] using safe
    obtain ⟨address, bound, stored⟩ := State.lookup_binds (related target repr visible)
    let after := {state with heap := state.heap.set address (.cell (repr.encode (Denote.term value env)))}
    obtain ⟨finalState, executed⟩ := ih after (Denote.term value env, env) ((Safety.term value model).1, model)
      (related.assign bindings (names.get target) address bound repr _) (bindings.write address _)
      (values.cons repr _ _ (input.scalarCore.value model env values)) (free.withHeap _) parts.2
    exact ⟨finalState, ExecutesBlock.next
      (assign_expression (input.sound program interp state env model related values free parts.1)
        bound (bindings.allocated bound) targetSpan span) rfl executed⟩
  | block body span rest ih =>
    obtain ⟨after, executed⟩ := ih state env model related bindings values free safe
    exact ⟨{ after with env := state.env }, ExecutesBlock.stop (ExecutesStatement.block executed span) rest (by intro h; cases h)⟩
  | emptyBlock next span ih =>
    obtain ⟨after, executed⟩ := ih state env model related bindings values free safe
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.block (ExecutesBlock.nil program state) span) rfl executed⟩
  | @if_ Γ t names scalar condition yes no rest test a b input yesBody noBody span ihy ihn =>
    have testValue : (Safety.term test model).1 = Denote.term test env := input.scalarCore.value model env values
    have parts : (Safety.term test model).2 = true ∧
        (if Denote.term test env then Safety.term a model else Safety.term b model).2 = true := by
      simpa only [Safety.term, testValue, Bool.and_eq_true] using safe
    have evaluated := input.sound program interp state env model related values free parts.1
    cases value : Denote.term test env
    · obtain ⟨after, executed⟩ := ihn state env model related bindings values free (by simpa [value] using parts.2)
      have branch : ExecutesBlock program state
          ((if (Scalar.bool.encode (Denote.term test env)).truthy then yes else no) :: rest)
          { control := .returned, value := scalar.encode (Denote.term b env), state := after } := by
        simpa [Scalar.encode, Value.truthy, value] using executed
      exact ⟨after, by simpa [Denote.term, value] using ExecutesBlock.if_ evaluated branch span⟩
    · obtain ⟨after, executed⟩ := ihy state env model related bindings values free (by simpa [value] using parts.2)
      have branch : ExecutesBlock program state
          ((if (Scalar.bool.encode (Denote.term test env)).truthy then yes else no) :: rest)
          { control := .returned, value := scalar.encode (Denote.term a env), state := after } := by
        simpa [Scalar.encode, Value.truthy, value] using executed
      exact ⟨after, by simpa [Denote.term, value] using ExecutesBlock.if_ evaluated branch span⟩

theorem guarded_statements_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (names : Names Γ) (scalar : Scalar t) (term : Term Γ t)
    (statements : List Stmt) (blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block statements blockSpan)
    (translation : GuardedStatements names scalar statements term)
    (interp : Named.Interp) (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : Environment names (bindArguments { heap } function.params args) env)
    (free : MathFree certificate.program (bindArguments { heap } function.params args))
    (data : Γ.all Safety.dataType = true)
    (safe : (Safety.term term (Safety.liftEnvironment Γ data env)).2 = true) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) := by
  obtain ⟨after, executed⟩ := translation.sound certificate.program interp _ env _ inputs
    (bindArguments_valid _ _ _) (Safety.scalar_lift_environment Γ data env) free safe
  apply certificate.transfer_from
  apply invoke_returned lookup
  rw [body]
  exact ExecutesStatement.block executed blockSpan

end Ariadne.Shallow.Adequacy

import Ariadne.Shallow.Adequacy.Function
import Ariadne.StatementConvergence
import Ariadne.Bindings

namespace Ariadne.Shallow.Adequacy
open Core

def Names.cons (name : String) (names : Names Γ) : Names (t :: Γ) :=
  { get := fun v => match v with | .here => name | .there v => names.get v
    visible := fun v => match v with | .here => true | .there v => names.visible v && names.get v != name }

theorem Environment.declare {interp : Named.Interp} {names : Names Γ} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (name : String) (scalar : Scalar t) (value : t.denote interp) :
    Environment (names.cons name) (state.declare name (scalar.encode value)) (value, env) := by
  intro u v repr visible
  cases v with
  | here => cases scalar <;> cases repr <;> exact lookup_declare_self ..
  | there v =>
    have facts : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
    exact lookup_declare_other (Ne.symm facts.2) (related v repr facts.1)

theorem Environment.assign {interp : Named.Interp} {names : Names Γ} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (bindings : state.ValidBindings)
    (name : String) (address : Nat) (bound : state.Binds name address)
    (scalar : Scalar t) (value : t.denote interp) :
    Environment (names.cons name)
      {state with heap := state.heap.set address (.cell (scalar.encode value))} (value, env) := by
  intro u v repr visible
  cases v with
  | here => cases scalar <;> cases repr <;> exact State.lookup_written_self bound (bindings.allocated bound) _
  | there v =>
    have facts : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
    exact State.lookup_written_other bindings bound (Ne.symm facts.2) (related v repr facts.1) _

theorem assign_expression {program : Program} {state : State} {expression : Expr} {value : Value}
    {name : String} {address : Nat}
    (input : Evaluates program state expression value state) (bound : state.Binds name address)
    (allocated : address < state.heap.length) (targetSpan span : Span) :
    ExecutesStatement program state (.assign (.var name targetSpan) expression span)
      { state := {state with heap := state.heap.set address (.cell value)} } := by
  obtain ⟨_, fuel, evaluated⟩ := input
  refine ⟨(by intro h; cases h), fuel + 2, ?_⟩
  simp [exec, assignTarget, evaluated, State.assign_bound bound allocated value, bind, Except.bind, pure, Except.pure]

/-- Returned statement sequences related to the actual typed Core body. Local
bindings extend both environments; early returns discard the source suffix. -/
inductive ScalarStatements : {Γ : List Core.Ty} → Names Γ → {t : Core.Ty} → Scalar t →
    List Stmt → Term Γ t → Prop where
  | return_ {names : Names Γ} {scalar : Scalar t} {expression : Expr} {term : Term Γ t}
      (input : ScalarExpr names scalar expression term) (span : Span) (rest : List Stmt) :
      ScalarStatements names scalar (.return_ expression span :: rest) term
  | let_ {names : Names Γ} {scalar : Scalar t} {repr : Scalar a} {expression : Expr}
      {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
      (name : String) (input : ScalarExpr names repr expression value)
      (next : ScalarStatements (names.cons name) scalar rest body)
      (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
      ScalarStatements names scalar (.let_ mutable name annotation expression span :: rest) (.let_ name value body)
  | assign {names : Names Γ} {scalar : Scalar t} {repr : Scalar a} {expression : Expr}
      {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
      (target : Var Γ a) (visible : names.visible target = true)
      (input : ScalarExpr names repr expression value)
      (next : ScalarStatements (names.cons (names.get target)) scalar rest body)
      (targetSpan span : Span) :
      ScalarStatements names scalar (.assign (.var (names.get target) targetSpan) expression span :: rest)
        (.let_ (names.get target) value body)
  | block {names : Names Γ} {scalar : Scalar t} {statements : List Stmt} {term : Term Γ t}
      (body : ScalarStatements names scalar statements term) (span : Span) (rest : List Stmt) :
      ScalarStatements names scalar (.block statements span :: rest) term
  | emptyBlock {names : Names Γ} {scalar : Scalar t} {rest : List Stmt} {term : Term Γ t}
      (next : ScalarStatements names scalar rest term) (span : Span) :
      ScalarStatements names scalar (.block [] span :: rest) term
  | if_ {names : Names Γ} {scalar : Scalar t} {condition : Expr} {yes no : Stmt} {rest : List Stmt}
      {test : Term Γ .bool} {a b : Term Γ t}
      (input : ScalarExpr names .bool condition test)
      (yesBody : ScalarStatements names scalar (yes :: rest) a)
      (noBody : ScalarStatements names scalar (no :: rest) b) (span : Span) :
      ScalarStatements names scalar (.if_ condition yes no span :: rest) (.ite test a b)

theorem ScalarStatements.sound {names : Names Γ} {scalar : Scalar t} {statements : List Stmt} {term : Term Γ t}
    (translation : ScalarStatements names scalar statements term) (program : Program) (interp : Named.Interp)
    (state : State) (env : Core.Env Γ interp) (related : Environment names state env)
    (bindings : state.ValidBindings) :
    ∃ after, ExecutesBlock program state statements
      { control := .returned, value := scalar.encode (Denote.term term env), state := after } := by
  induction translation generalizing state with
  | return_ input span rest =>
    exact ⟨state, ExecutesBlock.stop (ExecutesStatement.return_ (input.sound program interp state env related) span) rest (by intro h; cases h)⟩
  | @let_ Γ t a names scalar repr expression value body rest name input next mutable annotation span ih =>
    obtain ⟨after, executed⟩ := ih (state.declare name (repr.encode (Denote.term value env)))
      (Denote.term value env, env) (related.declare name repr _) (bindings.declare name _)
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.let_ (input.sound program interp state env related) mutable name annotation span) rfl executed⟩
  | @assign Γ t a names scalar repr expression value body rest target visible input next targetSpan span ih =>
    obtain ⟨address, bound, stored⟩ := State.lookup_binds (related target repr visible)
    let after := {state with heap := state.heap.set address (.cell (repr.encode (Denote.term value env)))}
    obtain ⟨finalState, executed⟩ := ih after (Denote.term value env, env)
      (related.assign bindings (names.get target) address bound repr _) (bindings.write address _)
    exact ⟨finalState, ExecutesBlock.next
      (assign_expression (input.sound program interp state env related) bound (bindings.allocated bound) targetSpan span)
      rfl executed⟩
  | block body span rest ih =>
    obtain ⟨after, executed⟩ := ih state env related bindings
    exact ⟨{ after with env := state.env }, ExecutesBlock.stop (ExecutesStatement.block executed span) rest (by intro h; cases h)⟩
  | emptyBlock next span ih =>
    obtain ⟨after, executed⟩ := ih state env related bindings
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.block (ExecutesBlock.nil program state) span) rfl executed⟩
  | @if_ Γ t names scalar condition yes no rest test a b input yesBody noBody span ihy ihn =>
    cases value : Denote.term test env
    · obtain ⟨after, executed⟩ := ihn state env related bindings
      have branch : ExecutesBlock program state
          ((if (Scalar.bool.encode (Denote.term test env)).truthy then yes else no) :: rest)
          { control := .returned, value := scalar.encode (Denote.term b env), state := after } := by
        simpa [Scalar.encode, Value.truthy, value] using executed
      exact ⟨after, by simpa [Denote.term, value] using ExecutesBlock.if_ (input.sound program interp state env related) branch span⟩
    · obtain ⟨after, executed⟩ := ihy state env related bindings
      have branch : ExecutesBlock program state
          ((if (Scalar.bool.encode (Denote.term test env)).truthy then yes else no) :: rest)
          { control := .returned, value := scalar.encode (Denote.term a env), state := after } := by
        simpa [Scalar.encode, Value.truthy, value] using executed
      exact ⟨after, by simpa [Denote.term, value] using ExecutesBlock.if_ (input.sound program interp state env related) branch span⟩

/-- Function application preserves the returned value and restores the caller's
lexical environment, including when the body allocates local binding cells. -/
theorem invoke_returned {program : Program} {function : Ariadne.Function} {before after : State}
    {args : List Value} {value : Value}
    (lookup : program.functions.find? (fun f => f.name == function.name) = some function)
    (returned : ExecutesStatement program (bindArguments before function.params args) function.body
      { control := .returned, value, state := after }) :
    Invokes program before (.function function.name) args value { after with env := before.env } := by
  obtain ⟨_, fuel, executed⟩ := returned
  refine ⟨(by intro h; cases h), fuel + 2, ?_⟩
  simp only [apply, lookup, callBody]
  change (exec program fuel (bindArguments before function.params args) function.body).bind (fun out =>
    if out.control == Control.broke || out.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (out.value, { out.state with env := before.env })) = _
  dsimp only at executed
  rw [executed]
  rfl

theorem bindArguments_valid (state : State) (params : List Param) (args : List Value) :
    (bindArguments state params args).ValidBindings := by
  have step : ∀ (entries : List (Param × Value)) (before : State), before.ValidBindings →
      (entries.foldl (fun state (param, value) => state.declare param.name value) before).ValidBindings := by
    intro entries
    induction entries with
    | nil => intro before valid; exact valid
    | cons entry entries ih =>
      intro before valid
      exact ih _ (valid.declare entry.1.name entry.2)
  exact step (params.zip args) _ (State.binds_empty state)

/-- Source transfer through a returned statement sequence. The kernel checks
both its source syntax and its actual Core body. -/
theorem scalar_statements_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (names : Names Γ) (scalar : Scalar t) (term : Term Γ t)
    (statements : List Stmt) (blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block statements blockSpan)
    (translation : ScalarStatements names scalar statements term)
    (interp : Named.Interp) (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : Environment names (bindArguments { heap } function.params args) env) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) := by
  obtain ⟨after, executed⟩ := translation.sound certificate.program interp _ env inputs (bindArguments_valid _ _ _)
  apply certificate.transfer_from
  apply invoke_returned lookup
  rw [body]
  exact ExecutesStatement.block executed blockSpan

end Ariadne.Shallow.Adequacy

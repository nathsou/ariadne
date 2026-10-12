import Ariadne.Shallow.Adequacy.Function
import Ariadne.StatementConvergence
namespace Ariadne.Shallow.Adequacy
open Core

def Names.cons (name : String) (names : Names Γ) : Names (t :: Γ) :=
  ⟨fun v => match v with | .here => name | .there v => names.get v⟩

def Names.Fresh (names : Names Γ) (name : String) : Prop := ∀ {t} (v : Var Γ t), name ≠ names.get v

theorem Environment.declare {interp : Named.Interp} {names : Names Γ} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (name : String) (scalar : Scalar t) (value : t.denote interp)
    (fresh : names.Fresh name) :
    Environment (names.cons name) (state.declare name (scalar.encode value)) (value, env) := by
  intro u v repr
  cases v with
  | here => cases scalar <;> cases repr <;> exact lookup_declare_self ..
  | there v => exact lookup_declare_other (fresh v) (related v repr)

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
      (fresh : names.Fresh name) (next : ScalarStatements (names.cons name) scalar rest body)
      (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
      ScalarStatements names scalar (.let_ mutable name annotation expression span :: rest) (.let_ name value body)
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
    (state : State) (env : Core.Env Γ interp) (related : Environment names state env) :
    ∃ after, ExecutesBlock program state statements
      { control := .returned, value := scalar.encode (Denote.term term env), state := after } := by
  induction translation generalizing state with
  | return_ input span rest =>
    exact ⟨state, ExecutesBlock.stop (ExecutesStatement.return_ (input.sound program interp state env related) span) rest (by intro h; cases h)⟩
  | @let_ Γ t a names scalar repr expression value body rest name input fresh next mutable annotation span ih =>
    obtain ⟨after, executed⟩ := ih (state.declare name (repr.encode (Denote.term value env)))
      (Denote.term value env, env) (related.declare name repr _ fresh)
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.let_ (input.sound program interp state env related) mutable name annotation span) rfl executed⟩
  | block body span rest ih =>
    obtain ⟨after, executed⟩ := ih state env related
    exact ⟨{ after with env := state.env }, ExecutesBlock.stop (ExecutesStatement.block executed span) rest (by intro h; cases h)⟩
  | emptyBlock next span ih =>
    obtain ⟨after, executed⟩ := ih state env related
    exact ⟨after, ExecutesBlock.next (ExecutesStatement.block (ExecutesBlock.nil program state) span) rfl executed⟩
  | @if_ Γ t names scalar condition yes no rest test a b input yesBody noBody span ihy ihn =>
    cases value : Denote.term test env
    · obtain ⟨after, executed⟩ := ihn state env related
      have branch : ExecutesBlock program state
          ((if (Scalar.bool.encode (Denote.term test env)).truthy then yes else no) :: rest)
          { control := .returned, value := scalar.encode (Denote.term b env), state := after } := by
        simpa [Scalar.encode, Value.truthy, value] using executed
      exact ⟨after, by simpa [Denote.term, value] using ExecutesBlock.if_ (input.sound program interp state env related) branch span⟩
    · obtain ⟨after, executed⟩ := ihy state env related
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
  obtain ⟨after, executed⟩ := translation.sound certificate.program interp _ env inputs
  apply certificate.transfer_from
  apply invoke_returned lookup
  rw [body]
  exact ExecutesStatement.block executed blockSpan

end Ariadne.Shallow.Adequacy

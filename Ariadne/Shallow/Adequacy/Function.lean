import Ariadne.Shallow.Adequacy.Scalar
import Ariadne.SourceFrom

namespace Ariadne.Shallow.Adequacy
open Core

/-- The operational call-frame binding used by `callBody`, named here so
entry-point proofs can establish their environment relation independently. -/
def bindArguments (state : State) (params : List Param) (args : List Value) : State :=
  (params.zip args).foldl (fun state (param, value) => state.declare param.name value) { state with env := [] }

theorem lookup_declare_self (state : State) (name : String) (value : Value) :
    (state.declare name value).lookup name = .ok value := by
  simp [State.lookup, State.declare, State.alloc, pure, Except.pure]

theorem lookup_declare_other {state : State} {name query : String} {value result : Value}
    (distinct : name ≠ query) (lookup : state.lookup query = .ok result) :
    (state.declare name value).lookup query = .ok result := by
  unfold State.lookup at lookup ⊢
  have different : (name == query) = false := by simp [distinct]
  simp only [State.declare, State.alloc, List.find?_cons, different]
  cases found : state.env.find? (fun p => p.1 == query) with
  | none => simp [found] at lookup
  | some entry =>
    rcases entry with ⟨_, address⟩
    cases cell : state.heap[address]? with
    | none => simp [found, cell] at lookup
    | some object =>
      have bound := (List.getElem?_eq_some_iff.mp cell).choose
      simpa only [found, List.getElem?_append_left bound] using lookup

theorem return_expression {program : Program} {state : State} {expression : Expr} {value : Value}
    (evaluated : Evaluates program state expression value state) (returnSpan blockSpan : Span) :
    Converges (fun fuel => exec program fuel state (.block [.return_ expression returnSpan] blockSpan))
      (.ok { control := .returned, value, state }) := by
  rcases evaluated.2 with ⟨fuel, evaluated⟩
  refine ⟨(by intro h; cases h), fuel + 3, ?_⟩
  simp [exec, execBlock, evaluated, bind, Except.bind, pure, Except.pure]
  rfl

theorem invoke_return {program : Program} {function : Ariadne.Function} {before : State}
    {args : List Value} {expression : Expr} {value : Value} {returnSpan blockSpan : Span}
    (lookup : program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.return_ expression returnSpan] blockSpan)
    (evaluated : Evaluates program (bindArguments before function.params args) expression value
      (bindArguments before function.params args)) :
    Invokes program before (.function function.name) args value
      { bindArguments before function.params args with env := before.env } := by
  rcases return_expression evaluated returnSpan blockSpan with ⟨_, fuel, returned⟩
  refine ⟨(by intro h; cases h), fuel + 2, ?_⟩
  simp only [apply, lookup, callBody, body]
  change (exec program fuel (bindArguments before function.params args)
      (.block [.return_ expression returnSpan] blockSpan)).bind (fun out =>
    if out.control == Control.broke || out.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (out.value, { out.state with env := before.env })) = _
  dsimp only at returned
  rw [returned]
  rfl

/-- Source transfer for a returned scalar expression. The correspondence witness
is about the actual function body; the environment premise only concerns
parameter cells. No premise assumes execution of the whole function. -/
theorem scalar_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (names : Names Γ) (scalar : Scalar t) (term : Term Γ t)
    (expression : Expr) (returnSpan blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.return_ expression returnSpan] blockSpan)
    (translation : ScalarExpr names scalar expression term)
    (interp : Named.Interp) (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : Environment names (bindArguments { heap } function.params args) env) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) := by
  apply certificate.transfer_from
  exact invoke_return lookup body (translation.sound _ interp _ env inputs)

end Ariadne.Shallow.Adequacy

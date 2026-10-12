import Ariadne.Convergence
import Ariadne.SourceFrom

namespace Ariadne

def EvaluatesArgs (program : Program) (before : State) (expressions : List Expr)
    (values : List Value) (after : State) : Prop :=
  Converges (fun fuel => evalArgs program fuel before expressions) (.ok (values, after))

theorem EvaluatesArgs.eventually {program : Program} {before after : State}
    {expressions : List Expr} {values : List Value} (h : EvaluatesArgs program before expressions values after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → evalArgs program fuel before expressions = .ok (values, after) :=
  ((converges_iff_eventually _ (fun h => evalArgs_fuel_mono program h before expressions) _).mp h).2

theorem EvaluatesArgs.nil (program : Program) (state : State) : EvaluatesArgs program state [] [] state :=
  ⟨(by intro h; cases h), 1, rfl⟩

theorem EvaluatesArgs.cons {program : Program} {before middle after : State}
    {expression : Expr} {rest : List Expr} {value : Value} {values : List Value}
    (head : Evaluates program before expression value middle)
    (tail : EvaluatesArgs program middle rest values after) :
    EvaluatesArgs program before (expression :: rest) (value :: values) after := by
  obtain ⟨nh, hh⟩ := head.eventually
  obtain ⟨nt, ht⟩ := tail.eventually
  refine ⟨(by intro h; cases h), max nh nt + 1, ?_⟩
  simp [evalArgs, hh _ (Nat.le_max_left ..), ht _ (Nat.le_max_right ..), bind, Except.bind, pure, Except.pure]

theorem Evaluates.call {program : Program} {before selected ready after : State}
    {callee : Expr} {args : List Expr} {target value : Value} {values : List Value}
    (function : Evaluates program before callee target selected)
    (arguments : EvaluatesArgs program selected args values ready)
    (invoked : Invokes program ready target values value after) (span : Span) :
    Evaluates program before (.call callee args span) value after := by
  obtain ⟨nf, hf⟩ := function.eventually
  obtain ⟨na, ha⟩ := arguments.eventually
  obtain ⟨ni, hi⟩ := invoked.eventually
  let n := max nf (max na ni)
  have hf' := hf n (Nat.le_max_left ..)
  have ha' := ha n (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..))
  have hi' := hi n (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))
  refine ⟨(by intro h; cases h), n + 1, ?_⟩
  simp [evalExpr, hf', ha', hi', bind, Except.bind]

theorem Evaluates.global (program : Program) (state : State) (name : String)
    (absent : state.env.any (fun p => p.1 == name) = false)
    (ordinary : name ≠ "NaN" ∧ name ≠ "Infinity") (span : Span) :
    Evaluates program state (.var name span) (.function name) state := by
  refine ⟨(by intro h; cases h), 1, ?_⟩
  simp [evalExpr, absent, ordinary.1, ordinary.2, pure, Except.pure]

theorem Invokes.scalar (program : Program) (state : State) (name : String) (args : List Value) (value : Value)
    (absent : program.functions.find? (fun f => f.name == name) = none)
    (primitive : invokeScalar name args = .ok value) :
    Invokes program state (.function name) args value state := by
  refine ⟨(by intro h; cases h), 1, ?_⟩
  simp [apply, absent, primitive, bind, Except.bind, pure, Except.pure]

end Ariadne

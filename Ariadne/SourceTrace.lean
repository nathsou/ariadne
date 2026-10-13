import Ariadne.SourceFrom

namespace Ariadne

/-- A finite sequence of calls in the original source evaluator. Each step
retains its actual heap and lexical environment for the following call. -/
inductive SourceTrace (source : String) : State → List (Value × List Value) → List Value → State → Prop where
  | nil (state : State) : SourceTrace source state [] [] state
  | next {before middle after : State} {target : Value} {args values : List Value}
      {value : Value} {calls : List (Value × List Value)}
      (call : SourceInvokes source before target args value middle)
      (rest : SourceTrace source middle calls values after) :
      SourceTrace source before ((target, args) :: calls) (value :: values) after

/-- Traces compose: running one call sequence and then another is running both. -/
theorem SourceTrace.append {source : String} {before middle after : State}
    {first second : List (Value × List Value)} {observed rest : List Value}
    (a : SourceTrace source before first observed middle) (b : SourceTrace source middle second rest after) :
    SourceTrace source before (first ++ second) (observed ++ rest) after := by
  induction a with
  | nil => exact b
  | next call _ ih => exact .next call (ih b)

/-- Call-sequence observations and final heaps are uniquely determined. -/
theorem SourceTrace.deterministic {source : String} {before : State}
    {calls : List (Value × List Value)} {left right : List Value} {afterLeft afterRight : State}
    (a : SourceTrace source before calls left afterLeft)
    (b : SourceTrace source before calls right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction a generalizing right afterRight with
  | nil => cases b; exact ⟨rfl, rfl⟩
  | next call rest ih =>
    cases b with
    | next other tail =>
      obtain ⟨rfl, rfl⟩ := call.deterministic other
      obtain ⟨rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl⟩

end Ariadne

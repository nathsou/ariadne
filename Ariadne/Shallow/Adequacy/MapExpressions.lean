import Ariadne.Shallow.Adequacy.MapScalarMutation
import Ariadne.CallConvergence

namespace Ariadne

theorem Value.beq_undefined (value : Value) : (value == .undefined) = decide (value = .undefined) := by
  cases value <;> rfl

theorem Value.beq_null (value : Value) : (value == .null) = decide (value = .null) := by
  cases value <;> rfl

theorem Evaluates.coalesce_nullish {program : Program} {before middle after : State}
    {left right : Expr} {a value : Value}
    (first : Evaluates program before left a middle)
    (second : Evaluates program middle right value after) (span : Span)
    (missing : a = .undefined ∨ a = .null) :
    Evaluates program before (.binary "??" left right span) value after := by
  obtain ⟨nl, hl⟩ := first.eventually
  obtain ⟨nr, hr⟩ := second.eventually
  refine ⟨(by intro h; cases h), max nl nr + 1, ?_⟩
  rcases missing with rfl | rfl <;>
    simp [evalExpr, hl _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), bind, Except.bind, pure, Except.pure, bne, Value.beq_undefined, Value.beq_null]

theorem Evaluates.coalesce_defined {program : Program} {before after : State}
    {left : Expr} {value : Value}
    (first : Evaluates program before left value after) (right : Expr) (span : Span)
    (defined : value ≠ .undefined ∧ value ≠ .null) :
    Evaluates program before (.binary "??" left right span) value after := by
  obtain ⟨_, fuel, evaluated⟩ := first
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [evalExpr, evaluated, defined, bind, Except.bind, pure, Except.pure, bne, Value.beq_undefined, Value.beq_null]

/-- Scalar Map set retains the caller's lexical environment. -/
theorem Invokes.map_set_env {program : Program} {state after : State} {address : Nat}
    {entries : List (Value × Value)} {key value : Value}
    (lookup : state.heap[address]? = some (.map entries))
    (invoked : Invokes program state (.method address "set") [key, value] (.ref address) after) :
    after.env = state.env := by
  have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have known : Invokes program state (.method address "set") [key, value] (.ref address)
      {state with heap := state.heap.set address (.map (mapSet entries key value))} := by
    refine ⟨(by intro h; cases h), 1, ?_⟩
    simp only [apply, lookup, State.write, allocated, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  obtain ⟨_, same⟩ := invoked.deterministic known
  simpa only using congrArg State.env same

end Ariadne

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Lookup with a bigint default is a proved expression over the original Map
method, including absent keys and actual scalar key equality. -/
theorem map_get_int_default [BEq κ] {keyCodec : Value → κ → Prop}
    {program : Program} {state : State} {address : Nat} {natives : JSMap κ Int} {owned : Footprint}
    (container keyExpr : Expr) (query : κ) (sourceKey : Value) (default : Int)
    (memberSpan callSpan defaultSpan coalesceSpan : Span)
    (input : (DataRelation.map (DataRelation.scalar keyCodec) DataRelation.int).Holds
      state.heap (.ref address) natives owned)
    (containerEval : Evaluates program state container (.ref address) state)
    (keyEval : Evaluates program state keyExpr sourceKey state)
    (keys : ∀ {source native}, keyCodec source native → sameValueZero source sourceKey = (native == query)) :
    Evaluates program state
      (.binary "??" (.call (.member container "get" memberSpan) [keyExpr] callSpan)
        (.literal (.bigint default) defaultSpan) coalesceSpan)
      (.bigint ((natives.get query).getD default)) state := by
  obtain ⟨root, entries, children, same, lookup, _, _, _⟩ := map_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  have method : Evaluates program state (.member container "get" memberSpan) (.method address "get") state :=
    containerEval.member "get" memberSpan (by simp [readMember, lookup, pure, Except.pure])
  obtain ⟨value, footprint, invoked, _, represented⟩ := map_get input program query sourceKey
    (fun related => keys related.1)
  have evaluated := Evaluates.call method (EvaluatesArgs.cons keyEval (EvaluatesArgs.nil program state)) invoked callSpan
  cases found : natives.get query with
  | none =>
    simp only [DataRelation.option, found] at represented
    have same : value = .undefined := represented.1
    subst value
    exact evaluated.coalesce_nullish (Evaluates.literal program state (.bigint default) defaultSpan)
      coalesceSpan (Or.inl rfl)
  | some native =>
    simp only [DataRelation.option, found, DataRelation.int, DataRelation.scalar] at represented
    have same : value = .bigint native := represented.1
    subst value
    simpa [found] using evaluated.coalesce_defined (.literal (.bigint default) defaultSpan)
      coalesceSpan (by constructor <;> intro h <;> cases h)

end Ariadne.Shallow.Adequacy

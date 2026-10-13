import Ariadne.CallConvergence
import Ariadne.Shallow.Adequacy.RecordMutation
import Ariadne.Shallow.Adequacy.Focus
import Ariadne.Shallow.Prelude.ArrayUpdate

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Field update through a temporary array projection, with the original
statement semantics and the exact native indexed replacement. -/
theorem array_projection_record_update {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {program : Program} {state : State}
    {outer : Nat} {natives : List (α × β)} {owned : Footprint}
    {query : Float.Model} {old updated : α} {rest : β}
    (name op : String) (container keyExpr rhs : Expr) (delta value : Value)
    (indexSpan fieldSpan statementSpan : Span)
    (input : (DataRelation.field name (DataRelation.scalar codec) tail).record.array.Holds
      state.heap (.ref outer) natives owned)
    (found : JSArray.get natives query = some (old, rest))
    (independent : IgnoresField tail name)
    (containerEval : Evaluates program state container (.ref outer) state)
    (keyEval : Evaluates program state keyExpr (.number query) state)
    (operandEval : Evaluates program state rhs delta state)
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ address after,
      ExecutesStatement program state
        (.update (.member (.index container keyExpr indexSpan) name fieldSpan) op rhs statementSpan) {state := after} ∧
      (DataRelation.field name (DataRelation.scalar codec) tail).record.array.Holds after.heap (.ref outer)
        (JSArray.map (fun item position => if position == query then (updated, rest) else item) natives) owned ∧
      Modifies [address] state.heap after.heap := by
  cases converted : indexOf (.number query) with
  | none => simp [JSArray.get, converted] at found
  | some index =>
    have selected : natives[index]? = some (old, rest) := by simpa [JSArray.get, converted] using found
    obtain ⟨root, runtime, children, same, lookup, elements, rootFresh, footprint⟩ := array_contents input
    have sameRoot : outer = root := Value.ref.inj same
    subst root
    obtain ⟨receiver, selectedFootprint, runtimeFound, subset, represented, rebuild⟩ :=
      elements.focus index (old, rest) selected
    obtain ⟨address, _, _, receiverEq, _, _, _, selectedEq⟩ := record_contents represented
    subst receiver
    have read : readIndex state (.ref outer) (.number query) = .ok (.ref address) := by
      simp [readIndex, converted, lookup, runtimeFound, pure, Except.pure]
    have projected := Evaluates.index containerEval keyEval indexSpan read
    obtain ⟨fields, after, fieldLookup, written, updatedRecord, writes⟩ :=
      record_scalar_set name value represented independent encoded
    obtain ⟨before, _, fieldRead, _, fieldRelated⟩ := record_get represented
      (ReadsField.required_head name (DataRelation.scalar codec) tail)
    have executed := ExecutesStatement.update
      (UpdatesTarget.record projected fieldRead operandEval (operation before fieldRelated.1)
        fieldLookup written fieldSpan) statementSpan
    have addressMember : address ∈ selectedFootprint := by rw [selectedEq]; simp
    have writesSelected : Modifies selectedFootprint state.heap after.heap := by
      refine ⟨writes.1, ?_⟩
      intro location allocated outside
      apply writes.2 location allocated
      intro member
      simp only [List.mem_singleton] at member
      subst location
      exact outside addressMember
    have updatedElements := rebuild after.heap (updated, rest) updatedRecord writesSelected
    have outside : outer ∉ selectedFootprint := fun member => rootFresh (subset member)
    have allocated : outer < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
    have unchanged := writesSelected.2 outer allocated outside
    have replacement := JSArray.map_replace_eq_set natives query index (updated, rest)
      input.1 converted (List.getElem?_eq_some_iff.mp selected).choose
    refine ⟨address, after, executed, ?_, writes⟩
    rw [replacement, footprint]
    refine ⟨?_, outer, .array runtime, children, rfl, unchanged.symm.trans lookup,
      ⟨runtime, rfl, updatedElements⟩, rootFresh, rfl⟩
    simpa only [List.length_set] using input.1
/-- Map field update retains the selected record reference and the ordered keys. -/
theorem map_projection_record_update [BEq key] {keyCodec : Value → key → Prop}
    {codec : Value → α → Prop} {tail : DataRelation (List (String × Value)) β}
    {program : Program} {state : State} {outer : Nat} {natives : JSMap key (α × β)} {owned : Footprint}
    {query : key} {sourceQuery : Value} {old updated : α} {rest : β}
    (name op : String) (container keyExpr rhs : Expr) (delta value : Value)
    (getMember getCall assertion fieldSpan statementSpan : Span)
    (input : (DataRelation.map (DataRelation.scalar keyCodec)
      (DataRelation.field name (DataRelation.scalar codec) tail).record).Holds
      state.heap (.ref outer) natives owned)
    (found : natives.get query = some (old, rest))
    (keys : ∀ {source native}, keyCodec source native → sameValueZero source sourceQuery = (native == query))
    (independent : IgnoresField tail name)
    (containerEval : Evaluates program state container (.ref outer) state)
    (keyEval : Evaluates program state keyExpr sourceQuery state)
    (operandEval : Evaluates program state rhs delta state)
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ address after,
      ExecutesStatement program state
        (.update (.member (.unary "#nonNull" (.call (.member container "get" getMember)
          [keyExpr] getCall) assertion) name fieldSpan) op rhs statementSpan) {state := after} ∧
      (DataRelation.map (DataRelation.scalar keyCodec)
        (DataRelation.field name (DataRelation.scalar codec) tail).record).Holds after.heap (.ref outer)
        (natives.set query (updated, rest)) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨root, runtime, children, same, lookup, elements, rootFresh, footprint⟩ := map_contents input
  have sameRoot : outer = root := Value.ref.inj same
  subst root
  obtain ⟨receiver, selectedFootprint, runtimeFound, subset, represented, rebuild⟩ :=
    elements.focusKey query sourceQuery (old, rest) found keys
  obtain ⟨address, _, _, receiverEq, _, _, _, selectedEq⟩ := record_contents represented
  subst receiver
  rw [receiverEq] at represented rebuild
  have methodEval : Evaluates program state (.member container "get" getMember) (.method outer "get") state :=
    containerEval.member "get" getMember (by simp [readMember, lookup, pure, Except.pure])
  have invoked : Invokes program state (.method outer "get") [sourceQuery] (.ref address) state := by
    refine ⟨(by intro h; cases h), 1, ?_⟩
    simp [apply, lookup, receiverEq, pure, Except.pure]
  have projected := (Evaluates.call methodEval
    (EvaluatesArgs.cons keyEval (EvaluatesArgs.nil program state)) invoked getCall).unary
      "#nonNull" assertion (by rfl)
  obtain ⟨fields, after, fieldLookup, written, updatedRecord, writes⟩ :=
    record_scalar_set name value represented independent encoded
  obtain ⟨before, _, fieldRead, _, fieldRelated⟩ := record_get represented
    (ReadsField.required_head name (DataRelation.scalar codec) tail)
  have executed := ExecutesStatement.update
    (UpdatesTarget.record projected fieldRead operandEval (operation before fieldRelated.1)
      fieldLookup written fieldSpan) statementSpan
  have addressMember : address ∈ selectedFootprint := by rw [selectedEq]; simp
  have writesSelected : Modifies selectedFootprint state.heap after.heap := by
    refine ⟨writes.1, ?_⟩
    intro location allocated outside
    apply writes.2 location allocated
    intro member
    simp only [List.mem_singleton] at member
    subst location
    exact outside addressMember
  have updatedElements := rebuild after.heap (updated, rest) updatedRecord writesSelected
  have outside : outer ∉ selectedFootprint := fun member => rootFresh (subset member)
  have allocated : outer < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have unchanged := writesSelected.2 outer allocated outside
  refine ⟨address, after, executed, ?_, writes⟩
  rw [footprint]
  exact ⟨outer, .map runtime, children, rfl, unchanged.symm.trans lookup,
    ⟨runtime, rfl, updatedElements⟩, rootFresh, rfl⟩

end Ariadne.Shallow.Adequacy

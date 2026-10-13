import Ariadne.Shallow.Adequacy.ProjectionMutation
import Ariadne.CallConvergence
import Ariadne.StatementConvergence
import Ariadne.Shallow.Adequacy.Function
import Ariadne.Ownership.Source

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Source execution and an observation of a caller-owned value in the final
heap. This records stateful effects rather than only a scalar return value. -/
def SourceMutatesFrom (source name : String) (heap : Heap) (args : List Value)
    (layout : DataRelation Value α) (receiver : Value) (native : α) : Prop :=
  ∃ after, SourceInvokes source {heap} (.function name) args .undefined after ∧
    Represents layout after.heap receiver native

def WrappedSourceMutatesFrom (source wrapperText name : String) (heap : Heap) (args : List Value)
    (layout : DataRelation Value α) (receiver : Value) (native : α) : Prop :=
  ∃ wrapper : Ownership.WrapperCertificate source, wrapper.text = wrapperText ∧
    ∃ entry : Ownership.EntryCertificate wrapper name, ∃ after,
      Ownership.GuardedInvokes wrapper.original.program entry.plan {heap} name args .undefined after ∧
        Represents layout after.heap receiver native

theorem transfer_mutation {source : String} {wrapper : Ownership.WrapperCertificate source}
    {name : String} (entry : Ownership.EntryCertificate wrapper name) {heap : Heap} {args : List Value}
    {layout : DataRelation Value α} {receiver : Value} {native : α}
    (original : SourceMutatesFrom source name heap args layout receiver native)
    (safe : Ownership.entrySafe wrapper.original.program entry.plan heap args = true) :
    WrappedSourceMutatesFrom source wrapper.text name heap args layout receiver native := by
  obtain ⟨after, ⟨program, checked, invoked⟩, related⟩ := original
  have same : program = wrapper.original.program :=
    Except.ok.inj (checked.symm.trans wrapper.original.checked)
  subst program
  exact ⟨wrapper, rfl, entry, after, Ownership.guarded_invokes_iff.mpr ⟨safe, invoked⟩, related⟩

/-- The source expression for a statement-scoped Map element push. Each span
is retained from the parsed source rather than reconstructed by the proof. -/
def mapPushExpression (container query value : Expr)
    (getMember getCall assertion pushMember pushCall : Span) : Expr :=
  .call (.member (.unary "#nonNull" (.call (.member container "get" getMember)
    [query] getCall) assertion) "push" pushMember) [value] pushCall

/-- Compose the primitive footprint proof with the actual source receiver,
key, assertion and method call. Operand premises concern subexpressions only;
none assumes evaluation of the complete mutation or function. -/
theorem map_push_expression [BEq key] {codec : Value → key → Prop} {relation : Value → α → Prop}
    {program : Program} {state : State} {outer : Nat} {natives : JSMap key (List α)} {owned : Footprint}
    {query : key} {sourceQuery : Value} {old : List α} {inserted : Value} {native : α}
    (container keyExpr valueExpr : Expr)
    (getMember getCall assertion pushMember pushCall : Span)
    (containerEval : Evaluates program state container (.ref outer) state)
    (keyEval : Evaluates program state keyExpr sourceQuery state)
    (valueEval : Evaluates program state valueExpr inserted state)
    (input : (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array).Holds
      state.heap (.ref outer) natives owned)
    (found : natives.get query = some old)
    (keys : ∀ {source native}, codec source native → sameValueZero source sourceQuery = (native == query))
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    ∃ (address : Nat) (after : State),
      Evaluates program state (mapPushExpression container keyExpr valueExpr
        getMember getCall assertion pushMember pushCall)
        (.number (Float.Model.ofNat (old ++ [native]).length)) after ∧
      (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array).Holds after.heap
        (.ref outer) (natives.set query (old ++ [native])) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨address, after, getInvoke, pushInvoke, updated, writes⟩ :=
    map_projection_push input found keys value capacity
  obtain ⟨root, entries, children, rootEq, mapLookup, _, _, _⟩ := map_contents input
  have sameRoot : outer = root := Value.ref.inj rootEq
  subst root
  have getMethod : Evaluates program state (.member container "get" getMember) (.method outer "get") state :=
    containerEval.member "get" getMember (by simp [readMember, mapLookup, pure, Except.pure])
  have getEval := Evaluates.call getMethod
    (EvaluatesArgs.cons keyEval (EvaluatesArgs.nil program state)) getInvoke getCall
  have asserted := getEval.unary "#nonNull" assertion (by rfl)
  obtain ⟨selected, footprint, selectedGet, _, related⟩ :=
    map_get input program query sourceQuery (fun h => keys h.1)
  have sameSelected := (selectedGet.deterministic getInvoke).1
  rw [sameSelected, found] at related
  change (DataRelation.scalar relation).array.Holds state.heap (.ref address) old footprint at related
  obtain ⟨child, runtime, _, childEq, childLookup, _, _, _⟩ := array_contents related
  have sameChild : address = child := Value.ref.inj childEq
  subst child
  have pushMethod : Evaluates program state
      (.member (.unary "#nonNull" (.call (.member container "get" getMember) [keyExpr] getCall) assertion)
        "push" pushMember) (.method address "push") state := asserted.member "push" pushMember
    (by simp [readMember, childLookup, pure, Except.pure])
  exact ⟨address, after, Evaluates.call pushMethod
    (EvaluatesArgs.cons valueEval (EvaluatesArgs.nil program state)) pushInvoke pushCall, updated, writes⟩

/-- The selected array value is a temporary statement borrow, and the final
native state is exactly the indexed replacement emitted by extraction. -/
def arrayPushExpression (container query value : Expr)
    (indexSpan pushMember pushCall : Span) : Expr :=
  .call (.member (.index container query indexSpan) "push" pushMember) [value] pushCall

theorem array_push_expression {relation : Value → α → Prop}
    {program : Program} {state : State} {outer : Nat} {natives : List (List α)} {owned : Footprint}
    {query : Float.Model} {old : List α} {inserted : Value} {native : α}
    (container keyExpr valueExpr : Expr) (indexSpan pushMember pushCall : Span)
    (containerEval : Evaluates program state container (.ref outer) state)
    (keyEval : Evaluates program state keyExpr (.number query) state)
    (valueEval : Evaluates program state valueExpr inserted state)
    (input : (DataRelation.scalar relation).array.array.Holds state.heap (.ref outer) natives owned)
    (found : JSArray.get natives query = some old)
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    ∃ (address : Nat) (after : State),
      Evaluates program state (arrayPushExpression container keyExpr valueExpr indexSpan pushMember pushCall)
        (.number (Float.Model.ofNat (old ++ [native]).length)) after ∧
      (DataRelation.scalar relation).array.array.Holds after.heap (.ref outer)
        (JSArray.map (fun item position => if position == query then old ++ [native] else item) natives) owned ∧
      Modifies [address] state.heap after.heap := by
  cases converted : indexOf (.number query) with
  | none => simp [JSArray.get, converted] at found
  | some index =>
    have selected : natives[index]? = some old := by simpa [JSArray.get, converted] using found
    obtain ⟨receiver, address, after, receiverEq, invoked, updated, writes, runtime, lookup, runtimeFound⟩ :=
      array_projection_push input selected value capacity
    subst receiver
    have read : readIndex state (.ref outer) (.number query) = .ok (.ref address) := by
      simp [readIndex, converted, lookup, runtimeFound, pure, Except.pure]
    have projected := Evaluates.index containerEval keyEval indexSpan read
    obtain ⟨root, actual, children, rootEq, rootLookup, elements, _, _⟩ := array_contents input
    have equal : outer = root := Value.ref.inj rootEq
    subst root
    obtain ⟨selectedValue, selectedFootprint, selectedFound, _, selectedRelated, _⟩ :=
      elements.focus index old selected
    have same : selectedValue = .ref address := by
      have sameRuntime : runtime = actual := Object.array.inj (Option.some.inj (lookup.symm.trans rootLookup))
      subst actual
      exact Option.some.inj (selectedFound.symm.trans runtimeFound)
    rw [same] at selectedRelated
    obtain ⟨child, _, _, childEq, childLookup, _, _, _⟩ := array_contents selectedRelated
    have sameChild : address = child := Value.ref.inj childEq
    subst child
    have pushMethod : Evaluates program state
        (.member (.index container keyExpr indexSpan) "push" pushMember) (.method address "push") state :=
      projected.member "push" pushMember (by simp [readMember, childLookup, pure, Except.pure])
    have replacement := JSArray.map_replace_eq_set natives query index (old ++ [native])
      input.1 converted (List.getElem?_eq_some_iff.mp selected).choose
    exact ⟨address, after, Evaluates.call pushMethod
      (EvaluatesArgs.cons valueEval (EvaluatesArgs.nil program state)) invoked pushCall,
      replacement.symm ▸ updated, writes⟩

theorem ExecutesStatement.expression {program : Program} {before after : State}
    {expression : Expr} {value : Value}
    (evaluated : Evaluates program before expression value after) (span : Span) :
    ExecutesStatement program before (.expr expression span) {state := after} := by
  obtain ⟨_, fuel, evaluated⟩ := evaluated
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [exec, evaluated, bind, Except.bind, pure, Except.pure]

/-- A single expression statement finishes normally with undefined, and both
its block and function restore lexical environments without changing the heap. -/
theorem invoke_expression {program : Program} {function : Ariadne.Function} {before after : State}
    {args : List Value} {expression : Expr} {value : Value} {statementSpan blockSpan : Span}
    (lookup : program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.expr expression statementSpan] blockSpan)
    (evaluated : Evaluates program (bindArguments before function.params args) expression value after) :
    Invokes program before (.function function.name) args .undefined {after with env := before.env} := by
  have head := ExecutesStatement.expression evaluated statementSpan
  have statements := ExecutesBlock.next head rfl (ExecutesBlock.nil program after)
  have block := ExecutesStatement.block statements blockSpan
  obtain ⟨_, fuel, executed⟩ := block
  refine ⟨(by intro h; cases h), fuel + 2, ?_⟩
  simp only [apply, lookup, callBody, body]
  change (exec program fuel (bindArguments before function.params args)
    (.block [.expr expression statementSpan] blockSpan)).bind (fun out =>
      if out.control == Control.broke || out.control == Control.continued then
        .error (Fault.invariant "loop control escaped a function")
      else .ok (out.value, {out.state with env := before.env})) = _
  dsimp only at executed
  rw [executed]
  rfl

theorem bindArguments_data {layout : DataRelation Value α} {state : State}
    {receiver : Value} {native : α} {footprint : Footprint}
    (related : layout.Holds state.heap receiver native footprint)
    (params : List Param) (args : List Value) :
    layout.Holds (bindArguments state params args).heap receiver native footprint := by
  have frame : ∀ pairs : List (Param × Value), ∀ state : State,
      layout.Holds state.heap receiver native footprint →
      layout.Holds (pairs.foldl (fun s (p, v) => s.declare p.name v) state).heap receiver native footprint := by
    intro pairs
    induction pairs with
    | nil => intro state related; exact related
    | cons pair rest ih =>
      intro state related
      apply ih
      exact layout.frame related (state.alloc_frame (.cell pair.2) footprint (layout.allocated related))
  exact frame (params.zip args) {state with env := []} related

theorem bindArguments_three (state : State) (first second third : Param) (a b c : Value)
    (firstSecond : first.name ≠ second.name) (firstThird : first.name ≠ third.name)
    (secondThird : second.name ≠ third.name) :
    (bindArguments state [first, second, third] [a, b, c]).lookup first.name = .ok a ∧
    (bindArguments state [first, second, third] [a, b, c]).lookup second.name = .ok b ∧
    (bindArguments state [first, second, third] [a, b, c]).lookup third.name = .ok c := by
  simp only [bindArguments, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil]
  exact ⟨lookup_declare_other firstThird.symm
      (lookup_declare_other firstSecond.symm (lookup_declare_self _ _ _)),
    lookup_declare_other secondThird.symm (lookup_declare_self _ _ _), lookup_declare_self _ _ _⟩

/-- A universal stateful source transfer for this syntax fragment. Its heap
premise is the actual input representation; it assumes neither whole-function
execution nor argument disjointness. -/
theorem map_push_source [BEq key] {codec : Value → key → Prop} {relation : Value → α → Prop}
    {source : String} (certificate : Certificate source) (function : Ariadne.Function)
    (heap : Heap) (args : List Value) (outer : Nat) (natives : JSMap key (List α)) (owned : Footprint)
    (query : key) (sourceQuery inserted : Value) (old : List α) (native : α)
    (containerName keyName valueName : String)
    (containerSpan keySpan valueSpan getMember getCall assertion pushMember pushCall statementSpan blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.expr (mapPushExpression
      (.var containerName containerSpan) (.var keyName keySpan) (.var valueName valueSpan)
      getMember getCall assertion pushMember pushCall) statementSpan] blockSpan)
    (containerLookup : (bindArguments {heap} function.params args).lookup containerName = .ok (.ref outer))
    (keyLookup : (bindArguments {heap} function.params args).lookup keyName = .ok sourceQuery)
    (valueLookup : (bindArguments {heap} function.params args).lookup valueName = .ok inserted)
    (input : (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array).Holds
      heap (.ref outer) natives owned)
    (found : natives.get query = some old)
    (keys : ∀ {source native}, codec source native → sameValueZero source sourceQuery = (native == query))
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    SourceMutatesFrom source function.name heap args
      (DataRelation.map (DataRelation.scalar codec) (DataRelation.scalar relation).array)
      (.ref outer) (natives.set query (old ++ [native])) := by
  let state := bindArguments {heap} function.params args
  have containerEval := Evaluates.variable certificate.program state containerName containerSpan
    (.ref outer) (State.lookup_present containerLookup) containerLookup
  have keyEval := Evaluates.variable certificate.program state keyName keySpan
    sourceQuery (State.lookup_present keyLookup) keyLookup
  have valueEval := Evaluates.variable certificate.program state valueName valueSpan
    inserted (State.lookup_present valueLookup) valueLookup
  obtain ⟨_, after, evaluated, updated, _⟩ := map_push_expression
    (.var containerName containerSpan) (.var keyName keySpan) (.var valueName valueSpan)
    getMember getCall assertion pushMember pushCall containerEval keyEval valueEval
    (bindArguments_data input function.params args) found keys value capacity
  exact ⟨{after with env := []}, certificate.transfer_invocation (invoke_expression lookup body evaluated),
    owned, updated⟩

/-- Array projection transfer observes the actual emitted indexed replacement
in the final source heap, under the same lookup and capacity guards. -/
theorem array_push_source {relation : Value → α → Prop}
    {source : String} (certificate : Certificate source) (function : Ariadne.Function)
    (heap : Heap) (args : List Value) (outer : Nat) (natives : List (List α)) (owned : Footprint)
    (query : Float.Model) (inserted : Value) (old : List α) (native : α)
    (containerName keyName valueName : String)
    (containerSpan keySpan valueSpan indexSpan pushMember pushCall statementSpan blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.expr (arrayPushExpression
      (.var containerName containerSpan) (.var keyName keySpan) (.var valueName valueSpan)
      indexSpan pushMember pushCall) statementSpan] blockSpan)
    (containerLookup : (bindArguments {heap} function.params args).lookup containerName = .ok (.ref outer))
    (keyLookup : (bindArguments {heap} function.params args).lookup keyName = .ok (.number query))
    (valueLookup : (bindArguments {heap} function.params args).lookup valueName = .ok inserted)
    (input : (DataRelation.scalar relation).array.array.Holds heap (.ref outer) natives owned)
    (found : JSArray.get natives query = some old)
    (value : relation inserted native) (capacity : (old ++ [native]).length < 2 ^ 32) :
    SourceMutatesFrom source function.name heap args (DataRelation.scalar relation).array.array
      (.ref outer) (JSArray.map (fun item position => if position == query then old ++ [native] else item) natives) := by
  let state := bindArguments {heap} function.params args
  have containerEval := Evaluates.variable certificate.program state containerName containerSpan
    (.ref outer) (State.lookup_present containerLookup) containerLookup
  have keyEval := Evaluates.variable certificate.program state keyName keySpan
    (.number query) (State.lookup_present keyLookup) keyLookup
  have valueEval := Evaluates.variable certificate.program state valueName valueSpan
    inserted (State.lookup_present valueLookup) valueLookup
  obtain ⟨_, after, evaluated, updated, _⟩ := array_push_expression
    (.var containerName containerSpan) (.var keyName keySpan) (.var valueName valueSpan)
    indexSpan pushMember pushCall containerEval keyEval valueEval
    (bindArguments_data input function.params args) found value capacity
  exact ⟨{after with env := []}, certificate.transfer_invocation (invoke_expression lookup body evaluated),
    owned, updated⟩

end Ariadne.Shallow.Adequacy

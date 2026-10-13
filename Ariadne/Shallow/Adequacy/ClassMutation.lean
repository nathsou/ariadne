import Ariadne.Shallow.Adequacy.RecordMutation
import Ariadne.Shallow.Adequacy.ProjectionSource

namespace Ariadne

theorem UpdatesTarget.instance_ {program : Program} {before selected operated after : State}
    {receiver rhs : Expr} {address : Nat} {field op className : String} {old delta value : Value}
    {fields : List (String × Value)}
    (selectedReceiver : Evaluates program before receiver (.ref address) selected)
    (read : readMember selected (.ref address) field = .ok old)
    (operand : Evaluates program selected rhs delta operated)
    (operation : binary op old delta = .ok value)
    (object : operated.heap[address]? = some (.instance_ className fields))
    (write : operated.write address (.instance_ className (fieldSet fields field value)) = .ok after)
    (span : Span) : UpdatesTarget program before (.member receiver field span) op rhs after := by
  obtain ⟨nr, hr⟩ := selectedReceiver.eventually
  obtain ⟨nd, hd⟩ := operand.eventually
  refine ⟨(by intro h; cases h), max nr nd + 1, ?_⟩
  simp [updateTarget, hr _ (Nat.le_max_left ..), hd _ (Nat.le_max_right ..),
    read, operation, object, write, bind, Except.bind]

theorem ExecutesStatement.assign_instance {program : Program} {before selected operated after : State}
    {receiver rhs : Expr} {address : Nat} {field className : String} {value : Value}
    {fields : List (String × Value)}
    (selectedReceiver : Evaluates program before receiver (.ref address) selected)
    (operand : Evaluates program selected rhs value operated)
    (object : operated.heap[address]? = some (.instance_ className fields))
    (write : operated.write address (.instance_ className (fieldSet fields field value)) = .ok after)
    (targetSpan span : Span) :
    ExecutesStatement program before (.assign (.member receiver field targetSpan) rhs span) {state := after} := by
  obtain ⟨nr, hr⟩ := selectedReceiver.eventually
  obtain ⟨nd, hd⟩ := operand.eventually
  refine ⟨(by intro h; cases h), max nr nd + 2, ?_⟩
  simp [exec, assignTarget, hr _ (Nat.le_max_left ..), hd _ (Nat.le_max_right ..),
    object, write, bind, Except.bind, pure, Except.pure]

/-- Invoke an actual class method, restoring the caller's lexical bindings. -/
theorem invoke_method_completion {program : Program} {class_ : Class} {method : Ariadne.Function}
    {before : State} {address : Nat} {fields : List (String × Value)} {args : List Value} {out : Completion}
    (receiver : before.heap[address]? = some (.instance_ class_.name fields))
    (classLookup : program.classes.find? (·.name == class_.name) = some class_)
    (methodLookup : class_.methods.find? (·.name == method.name) = some method)
    (body : ExecutesStatement program
      (Shallow.Adequacy.bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params)
        (.ref address :: args)) method.body out)
    (normal : out.control = .normal ∨ out.control = .returned) :
    Invokes program before (.method address method.name) args out.value {out.state with env := before.env} := by
  obtain ⟨_, fuel, executed⟩ := body
  refine ⟨(by intro h; cases h), fuel + 2, ?_⟩
  simp only [apply, receiver, classLookup, methodLookup, callBody]
  change (exec program fuel
      (Shallow.Adequacy.bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params)
        (.ref address :: args)) method.body).bind (fun result =>
    if result.control == Control.broke || result.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (result.value, {result.state with env := before.env})) = _
  dsimp only at executed
  rw [executed]
  rcases normal with normal | normal <;> simp [normal, Except.bind] <;> decide

end Ariadne

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

theorem class_contents {layout : DataRelation (List (String × Value)) α} {heap : Heap} {value : Value}
    {native : α} {footprint : Footprint} {className : String}
    (input : (layout.classState className).Holds heap value native footprint) :
    ∃ address fields children, value = .ref address ∧ heap[address]? = some (.instance_ className fields) ∧
      layout.Holds heap fields native children ∧ address ∉ children ∧ footprint = address :: children := by
  rcases input with ⟨address, object, children, hv, lookup, contents, fresh, eq⟩
  rcases contents with ⟨fields, project, related⟩
  cases object
  all_goals try contradiction
  case instance_ actual values =>
    by_cases same : actual = className
    · subst actual
      simp only [↓reduceIte] at project
      cases project
      exact ⟨address, fields, children, hv, lookup, related, fresh, eq⟩
    · simp [same] at project

theorem class_scalar_set {codec : Value → α → Prop} {tail : DataRelation (List (String × Value)) β}
    {state : State} {address : Nat} {old updated : α} {rest : β} {owned : Footprint}
    (className name : String) (value : Value)
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
      state.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name) (encoded : codec value updated) :
    ∃ fields after,
      state.heap[address]? = some (.instance_ className fields) ∧
      state.write address (.instance_ className (fieldSet fields name value)) = .ok after ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
        after.heap (.ref address) (updated, rest) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨root, fields, children, same, lookup, related, fresh, footprint⟩ := class_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  obtain ⟨oldValue, oldLookup, left, right, oldRelated, tailRelated, _, childrenEq⟩ := related
  obtain ⟨_, rfl⟩ := oldRelated
  simp only [List.nil_append] at childrenEq
  subst children
  let after := {state with heap := state.heap.set address (.instance_ className (fieldSet fields name value))}
  have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have written : state.write address (.instance_ className (fieldSet fields name value)) = .ok after := by
    simp [State.write, allocated, after]
  have framed := tail.frame (independent value tailRelated)
    (agreesOn_set state.heap right address (.instance_ className (fieldSet fields name value)) fresh)
  refine ⟨fields, after, lookup, written, ?_, State.write_modifies written⟩
  rw [footprint]
  refine ⟨address, .instance_ className (fieldSet fields name value), right, rfl, ?_, ?_, fresh, rfl⟩
  · simp [after, allocated]
  · exact ⟨fieldSet fields name value, (by simp), value, fieldSet_lookup_self fields name value,
      [], right, ⟨encoded, rfl⟩, framed, (by simp [Disjoint]), rfl⟩


/-- A required class field is read as data, rather than as a method. -/
theorem class_scalar_get {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {state : State}
    {address : Nat} {className name : String} {old : α} {rest : β} {owned : Footprint}
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
      state.heap (.ref address) (old, rest) owned) :
    ∃ before, readMember state (.ref address) name = .ok before ∧ codec before old := by
  obtain ⟨root, fields, children, same, lookup, related, _, _⟩ := class_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  obtain ⟨before, found, _, _, represented, _, _, _⟩ := related
  exact ⟨before, by simp [readMember, lookup, found, pure, Except.pure], represented.1⟩

/-- Class field updates frame private and public descendants uniformly. -/
theorem class_scalar_update {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {program : Program} {state : State}
    {address : Nat} {old updated : α} {rest : β} {owned : Footprint}
    (className name op : String) (receiver rhs : Expr) (delta value : Value)
    (targetSpan statementSpan : Span)
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
      state.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name)
    (receiverEval : Evaluates program state receiver (.ref address) state)
    (operandEval : Evaluates program state rhs delta state)
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ after,
      ExecutesStatement program state (.update (.member receiver name targetSpan) op rhs statementSpan) {state := after} ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
        after.heap (.ref address) (updated, rest) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨before, read, represented⟩ := class_scalar_get input
  obtain ⟨fields, after, lookup, written, related, modifies⟩ :=
    class_scalar_set className name value input independent encoded
  exact ⟨after, ExecutesStatement.update (UpdatesTarget.instance_ receiverEval read operandEval
    (operation before represented) lookup written targetSpan) statementSpan, related, modifies⟩

/-- Ordinary class field assignment also writes only the instance root. -/
theorem class_scalar_assign {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {program : Program} {state : State}
    {address : Nat} {old updated : α} {rest : β} {owned : Footprint}
    (className name : String) (receiver rhs : Expr) (value : Value)
    (targetSpan statementSpan : Span)
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
      state.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name)
    (receiverEval : Evaluates program state receiver (.ref address) state)
    (operandEval : Evaluates program state rhs value state) (encoded : codec value updated) :
    ∃ after,
      ExecutesStatement program state (.assign (.member receiver name targetSpan) rhs statementSpan) {state := after} ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState className).Holds
        after.heap (.ref address) (updated, rest) owned ∧
      Modifies [address] state.heap after.heap := by
  obtain ⟨fields, after, lookup, written, related, modifies⟩ :=
    class_scalar_set className name value input independent encoded
  exact ⟨after, ExecutesStatement.assign_instance receiverEval operandEval
    lookup written targetSpan statementSpan, related, modifies⟩

/-- Transfer a scalar update through the original checked class method. Only
subexpression evaluation and the primitive operator are premises. The result
observes the updated class layout in the actual heap after the method call. -/
theorem class_scalar_method_source {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {source : String}
    (certificate : Certificate source) (class_ : Class) (method : Ariadne.Function)
    (before : State) (address : Nat) (fields : List (String × Value)) (args : List Value)
    (old updated : α) (rest : β) (owned : Footprint)
    (name op : String) (rhs : Expr) (delta value : Value)
    (thisSpan targetSpan statementSpan blockSpan : Span)
    (receiver : before.heap[address]? = some (.instance_ class_.name fields))
    (classLookup : certificate.program.classes.find? (·.name == class_.name) = some class_)
    (methodLookup : class_.methods.find? (·.name == method.name) = some method)
    (body : method.body = .block [.update (.member (.var "this" thisSpan) name targetSpan) op rhs statementSpan] blockSpan)
    (thisLookup : (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params)
      (.ref address :: args)).lookup "this" = .ok (.ref address))
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
      before.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name)
    (operand : Evaluates certificate.program
      (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)) rhs delta
      (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)))
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ after, SourceInvokes source before (.method address method.name) args .undefined after ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
        after.heap (.ref address) (updated, rest) owned := by
  let state := bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)
  have thisEval := Evaluates.variable certificate.program state "this" thisSpan (.ref address)
    (State.lookup_present thisLookup) thisLookup
  obtain ⟨after, executed, related, modifies⟩ := class_scalar_update class_.name name op
    (.var "this" thisSpan) rhs delta value targetSpan statementSpan
    (bindArguments_data input _ _) independent thisEval operand operation encoded
  have block := ExecutesStatement.block
    (ExecutesBlock.next executed rfl (ExecutesBlock.nil certificate.program after)) blockSpan
  refine ⟨{after with env := before.env}, certificate.transfer_invocation ?_, related⟩
  exact invoke_method_completion receiver classLookup methodLookup (body.symm ▸ block) (Or.inl rfl)

/-- Transfer a scalar assignment through the original checked class method. Only
subexpression evaluation and scalar encoding are premises. The result
observes the updated class layout in the actual heap after the method call. -/
theorem class_scalar_assign_method_source {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {source : String}
    (certificate : Certificate source) (class_ : Class) (method : Ariadne.Function)
    (before : State) (address : Nat) (fields : List (String × Value)) (args : List Value)
    (old updated : α) (rest : β) (owned : Footprint)
    (name : String) (rhs : Expr) (value : Value)
    (thisSpan targetSpan statementSpan blockSpan : Span)
    (receiver : before.heap[address]? = some (.instance_ class_.name fields))
    (classLookup : certificate.program.classes.find? (·.name == class_.name) = some class_)
    (methodLookup : class_.methods.find? (·.name == method.name) = some method)
    (body : method.body = .block [.assign (.member (.var "this" thisSpan) name targetSpan) rhs statementSpan] blockSpan)
    (thisLookup : (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params)
      (.ref address :: args)).lookup "this" = .ok (.ref address))
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
      before.heap (.ref address) (old, rest) owned)
    (independent : IgnoresField tail name)
    (operand : Evaluates certificate.program
      (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)) rhs value
      (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)))
    (encoded : codec value updated) :
    ∃ after, SourceInvokes source before (.method address method.name) args .undefined after ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
        after.heap (.ref address) (updated, rest) owned := by
  let state := bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)
  have thisEval := Evaluates.variable certificate.program state "this" thisSpan (.ref address)
    (State.lookup_present thisLookup) thisLookup
  obtain ⟨after, executed, related, modifies⟩ := class_scalar_assign class_.name name
    (.var "this" thisSpan) rhs value targetSpan statementSpan
    (bindArguments_data input _ _) independent thisEval operand encoded
  have block := ExecutesStatement.block
    (ExecutesBlock.next executed rfl (ExecutesBlock.nil certificate.program after)) blockSpan
  refine ⟨{after with env := before.env}, certificate.transfer_invocation ?_, related⟩
  exact invoke_method_completion receiver classLookup methodLookup (body.symm ▸ block) (Or.inl rfl)

/-- Reading a required field invokes the original class method and preserves
its represented state, including all descendants and private fields. -/
theorem class_scalar_read_method_source {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {source : String}
    (certificate : Certificate source) (class_ : Class) (method : Ariadne.Function)
    (before : State) (address : Nat) (fields : List (String × Value)) (args : List Value)
    (old : α) (rest : β) (owned : Footprint) (name : String)
    (thisSpan fieldSpan returnSpan blockSpan : Span)
    (receiver : before.heap[address]? = some (.instance_ class_.name fields))
    (classLookup : certificate.program.classes.find? (·.name == class_.name) = some class_)
    (methodLookup : class_.methods.find? (·.name == method.name) = some method)
    (body : method.body = .block [.return_ (.member (.var "this" thisSpan) name fieldSpan) returnSpan] blockSpan)
    (thisLookup : (bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params)
      (.ref address :: args)).lookup "this" = .ok (.ref address))
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
      before.heap (.ref address) (old, rest) owned) :
    ∃ value after, SourceInvokes source before (.method address method.name) args value after ∧
      codec value old ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).classState class_.name).Holds
        after.heap (.ref address) (old, rest) owned := by
  let state := bindArguments before ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)
  have framed := bindArguments_data input ({name := "this", ty := .class_ class_.name} :: method.params) (.ref address :: args)
  obtain ⟨value, read, encoded⟩ := class_scalar_get framed
  have thisEval := Evaluates.variable certificate.program state "this" thisSpan (.ref address)
    (State.lookup_present thisLookup) thisLookup
  have executed := ExecutesStatement.block
    (ExecutesBlock.stop (ExecutesStatement.return_ (thisEval.member name fieldSpan read) returnSpan)
      [] (by intro h; cases h)) blockSpan
  exact ⟨value, {state with env := before.env}, certificate.transfer_invocation
    (invoke_method_completion receiver classLookup methodLookup (body.symm ▸ executed) (Or.inr rfl)), encoded, framed⟩

/-- Borrow one required field for a statement, then rebuild the enclosing
class relation. The instance retains its fields and runtime identity; mutation
is confined to the selected child's footprint. -/
theorem class_field_focus {head : DataRelation Value α}
    {tail : DataRelation (List (String × Value)) β} {className name : String}
    {state : State} {address : Nat} {old : α} {rest : β} {owned : Footprint}
    (input : ((DataRelation.field name head tail).classState className).Holds
      state.heap (.ref address) (old, rest) owned) :
    ∃ value selected,
      readMember state (.ref address) name = .ok value ∧ selected ⊆ owned ∧
      head.Holds state.heap value old selected ∧
      ∀ (after : Heap) (updated : α), head.Holds after value updated selected →
        Modifies selected state.heap after →
        ((DataRelation.field name head tail).classState className).Holds
          after (.ref address) (updated, rest) owned := by
  obtain ⟨root, fields, children, same, lookup, related, fresh, footprint⟩ := class_contents input
  have sameRoot : address = root := Value.ref.inj same
  subst root
  obtain ⟨value, found, selected, other, represented, remainder, separate, childrenEq⟩ := related
  subst children
  refine ⟨value, selected, by simp [readMember, lookup, found, pure, Except.pure], ?_, represented, ?_⟩
  · rw [footprint]
    intro location member
    simp [member]
  · intro after updated related modified
    have allocated : address < state.heap.length := (List.getElem?_eq_some_iff.mp lookup).choose
    have outside : address ∉ selected := fun member => fresh (by simp [member])
    have unchanged := modified.2 address allocated outside
    have framed := tail.frame remainder (modified.frame (tail.allocated remainder) separate.symm)
    rw [footprint]
    refine ⟨address, .instance_ className fields, selected ++ other, rfl, unchanged.symm.trans lookup,
      ?_, fresh, rfl⟩
    exact ⟨fields, by simp, value, found, selected, other, related, framed, separate, rfl⟩

end Ariadne.Shallow.Adequacy

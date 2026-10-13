import Ariadne.Shallow.Adequacy.ClassMutation
import Ariadne.CallConvergence

namespace Ariadne

/-- Field initializer evaluation has the same fuel stability as expressions. -/
theorem evalFields_fuel_mono (program : Program) {small large : Nat} (le : small ≤ large)
    (state : State) (fields : List (String × Expr)) (acc : List (String × Value)) :
    (evalFields program small state fields acc).Refines (evalFields program large state fields acc) := by
  have step : ∀ fuel state fields acc,
      (evalFields program fuel state fields acc).Refines (evalFields program (fuel + 1) state fields acc) := by
    intro fuel
    induction fuel with
    | zero => intro state fields acc; exact Or.inl rfl
    | succ fuel ih =>
      intro state fields acc
      cases fields with
      | nil => exact Result.Refines.refl _
      | cons field fields =>
        rcases field with ⟨name, expression⟩
        conv => lhs; unfold evalFields
        conv => rhs; unfold evalFields
        repeat' first
        | exact Result.Refines.refl _
        | exact evalExpr_fuel_mono program (Nat.le_succ _) _ _
        | exact ih _ _ _
        | apply Result.Refines.bind
        | intro x
        | dsimp only []
        | split
        | cases x
  exact Result.refines_of_step _ (fun fuel => step fuel state fields acc) le

def EvaluatesFields (program : Program) (before : State) (fields : List (String × Expr))
    (acc values : List (String × Value)) (after : State) : Prop :=
  Converges (fun fuel => evalFields program fuel before fields acc) (.ok (values, after))

theorem EvaluatesFields.eventually {program : Program} {before after : State}
    {fields : List (String × Expr)} {acc values : List (String × Value)}
    (evaluated : EvaluatesFields program before fields acc values after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → evalFields program fuel before fields acc = .ok (values, after) :=
  ((converges_iff_eventually _ (fun h => evalFields_fuel_mono program h before fields acc) _).mp evaluated).2

theorem EvaluatesFields.nil (program : Program) (state : State) (acc : List (String × Value)) :
    EvaluatesFields program state [] acc acc state := ⟨(by intro h; cases h), 1, rfl⟩

theorem EvaluatesFields.cons {program : Program} {before middle after : State}
    {name : String} {expression : Expr} {fields : List (String × Expr)}
    {acc values : List (String × Value)} {value : Value}
    (first : Evaluates program before expression value middle)
    (rest : EvaluatesFields program middle fields (fieldSet acc name value) values after)
    (named : name ≠ "") :
    EvaluatesFields program before ((name, expression) :: fields) acc values after := by
  obtain ⟨nf, hf⟩ := first.eventually
  obtain ⟨nr, hr⟩ := rest.eventually
  refine ⟨(by intro h; cases h), max nf nr + 1, ?_⟩
  simp [evalFields, hf _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), named,
    bind, Except.bind, pure, Except.pure]

/-- Execution of a call frame, used equally for methods and constructors. -/
def CompletesBody (program : Program) (before : State) (params : List Param) (body : Stmt)
    (args : List Value) (value : Value) (after : State) : Prop :=
  Converges (fun fuel => callBody program fuel before [] params body args) (.ok (value, after))

theorem CompletesBody.eventually {program : Program} {before after : State}
    {params : List Param} {body : Stmt} {args : List Value} {value : Value}
    (completed : CompletesBody program before params body args value after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → callBody program fuel before [] params body args = .ok (value, after) :=
  ((converges_iff_eventually _ (fun h => callBody_fuel_mono program h before [] params body args) _).mp completed).2

theorem CompletesBody.statement {program : Program} {before : State} {params : List Param}
    {body : Stmt} {args : List Value} {out : Completion}
    (executed : ExecutesStatement program (Shallow.Adequacy.bindArguments before params args) body out)
    (normal : out.control = .normal ∨ out.control = .returned) :
    CompletesBody program before params body args out.value {out.state with env := before.env} := by
  obtain ⟨_, fuel, evaluated⟩ := executed
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp only [callBody]
  dsimp only at evaluated
  change (exec program fuel (Shallow.Adequacy.bindArguments before params args) body).bind (fun result =>
    if result.control == Control.broke || result.control == Control.continued then
      .error (Fault.invariant "loop control escaped a function")
    else .ok (result.value, {result.state with env := before.env})) = _
  rw [evaluated]
  rcases normal with normal | normal <;> simp [normal, Except.bind] <;> decide

/-- Allocate a fresh instance after evaluating arguments and initializers once. -/
theorem Evaluates.newClass_plain {program : Program} {class_ : Class}
    {before ready initialized : State} {expressions : List Expr} {args : List Value}
    {fields : List (String × Value)}
    (lookup : program.classes.find? (·.name == class_.name) = some class_)
    (plain : class_.constructor_ = none)
    (arguments : EvaluatesArgs program before expressions args ready)
    (initializers : EvaluatesFields program ready (class_.fields.map fun f => (f.name, f.value)) [] fields initialized)
    (span : Span) :
    Evaluates program before (.newClass class_.name expressions span) (.ref initialized.heap.length)
      (initialized.alloc (.instance_ class_.name fields)).2 := by
  obtain ⟨na, ha⟩ := arguments.eventually
  obtain ⟨nf, hf⟩ := initializers.eventually
  refine ⟨(by intro h; cases h), max na nf + 1, ?_⟩
  simp [evalExpr, lookup, ha _ (Nat.le_max_left ..), hf _ (Nat.le_max_right ..), plain,
    State.alloc, bind, Except.bind, pure, Except.pure]

/-- A constructor executes in the newly allocated instance's call frame. -/
theorem Evaluates.newClass_constructor {program : Program} {class_ : Class} {constructor : Ariadne.Function}
    {before ready initialized after : State} {expressions : List Expr} {args : List Value}
    {fields : List (String × Value)} {result : Value}
    (lookup : program.classes.find? (·.name == class_.name) = some class_)
    (constructs : class_.constructor_ = some constructor)
    (arguments : EvaluatesArgs program before expressions args ready)
    (initializers : EvaluatesFields program ready (class_.fields.map fun f => (f.name, f.value)) [] fields initialized)
    (body : CompletesBody program (initialized.alloc (.instance_ class_.name fields)).2
      ({name := "this", ty := .class_ class_.name} :: constructor.params) constructor.body
      (.ref initialized.heap.length :: args) result after) (span : Span) :
    Evaluates program before (.newClass class_.name expressions span) (.ref initialized.heap.length) after := by
  obtain ⟨na, ha⟩ := arguments.eventually
  obtain ⟨nf, hf⟩ := initializers.eventually
  obtain ⟨nc, hc⟩ := body.eventually
  let fuel := max na (max nf nc)
  have ha' := ha fuel (Nat.le_max_left ..)
  have hf' := hf fuel (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..))
  have hc' := hc fuel (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp only [evalExpr, lookup, ha', hf', constructs, bind, Except.bind]
  simp only [State.alloc] at hc' ⊢
  rw [hc']
  rfl

theorem Evaluates.newMap (program : Program) (state : State) (key value : Ty) (span : Span) :
    Evaluates program state (.newMap key value span) (.ref state.heap.length) (state.alloc (.map [])).2 :=
  ⟨(by intro h; cases h), 1, rfl⟩

/-- Source-bound expression execution, including fresh class construction. -/
def SourceEvaluates (source : String) (before : State) (expression : Expr)
    (value : Value) (after : State) : Prop :=
  ∃ program, frontend source = .ok program ∧ Evaluates program before expression value after

theorem Certificate.transfer_evaluation {source : String} (certificate : Certificate source)
    {before after : State} {expression : Expr} {value : Value}
    (evaluated : Evaluates certificate.program before expression value after) :
    SourceEvaluates source before expression value after := ⟨_, certificate.checked, evaluated⟩

end Ariadne

namespace Ariadne.Shallow.DataRelation
open Heap

/-- A fresh object's children are framed across allocation; its new root
cannot alias any allocated child in the input relation. -/
theorem reference_alloc {contents : DataRelation Object α} {state : State} {object : Object}
    {native : α} {children : Footprint} (input : contents.Holds state.heap object native children) :
    contents.reference.Holds (state.alloc object).2.heap (.ref (state.alloc object).1) native
      ((state.alloc object).1 :: children) := by
  exact ⟨_, object, children, rfl, state.alloc_lookup object,
    contents.frame input (state.alloc_frame object children (contents.allocated input)),
    state.alloc_fresh object children (contents.allocated input), rfl⟩

theorem class_alloc {layout : DataRelation (List (String × Value)) α} {state : State}
    {className : String} {fields : List (String × Value)} {native : α} {children : Footprint}
    (input : layout.Holds state.heap fields native children) :
    (layout.classState className).Holds (state.alloc (.instance_ className fields)).2.heap
      (.ref state.heap.length) native (state.heap.length :: children) :=
  reference_alloc (contents := DataRelation.object
    (fun | .instance_ actual values => if actual = className then some values else none | _ => none) layout)
    ⟨fields, by simp, input⟩

/-- Empty Maps own only their freshly allocated root. -/
theorem map_alloc [BEq κ] (key : DataRelation Value κ) (value : DataRelation Value υ) (state : State) :
    (DataRelation.map key value).Holds (state.alloc (.map [])).2.heap (.ref state.heap.length)
      JSMap.empty [state.heap.length] :=
  reference_alloc (contents := DataRelation.object (fun | .map entries => some entries | _ => none)
    (key.product value).sequence) ⟨[], rfl, .nil⟩

end Ariadne.Shallow.DataRelation

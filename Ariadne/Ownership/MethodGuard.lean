import Ariadne.Ownership.Source

namespace Ariadne.Ownership

/-- A method guard includes the actual receiver as its first borrowed argument. -/
def checkedMethodApply (program : Program) (plan : List ArgumentCheck) (fuel : Nat)
    (before : State) (address : Nat) (name : String) (args : List Value) : Result (Value × State) := do
  checkArguments program plan before.heap (.ref address :: args)
  apply program fuel before (.method address name) args

def GuardedMethodInvokes (program : Program) (plan : List ArgumentCheck) (before : State)
    (address : Nat) (name : String) (args : List Value) (value : Value) (after : State) : Prop :=
  Converges (fun fuel => checkedMethodApply program plan fuel before address name args) (.ok (value, after))

theorem guarded_method_invokes_iff {program : Program} {plan : List ArgumentCheck}
    {before after : State} {address : Nat} {name : String} {args : List Value} {value : Value} :
    GuardedMethodInvokes program plan before address name args value after ↔
      entrySafe program plan before.heap (.ref address :: args) = true ∧
      Invokes program before (.method address name) args value after := by
  cases guard : checkArguments program plan before.heap (.ref address :: args) with
  | error error =>
    simp [GuardedMethodInvokes, checkedMethodApply, guard, Converges, entrySafe, Except.isOk,
      Except.toBool, bind, Except.bind]
  | ok result =>
    cases result
    simp only [GuardedMethodInvokes, checkedMethodApply, guard, bind, Except.bind,
      entrySafe, Except.isOk, Except.toBool, true_and]
    rfl

/-- The method plan uses the same class lowering as the certified renderer. -/
def methodEntryPlan (program : Program) (className : String) (method : Ariadne.Function) :
    Checked (List ArgumentCheck) := do
  let lowered ← Shallow.ClassPlan.lower program
  Wrap.methodPlan lowered className method

/-- Reuse the renderer's staged class-lowering equation when certifying methods. -/
theorem methodEntryPlan_of_lowered {program lowered : Program} {className : String}
    {method : Ariadne.Function} {plan : List ArgumentCheck}
    (classes : Shallow.ClassPlan.lower program = .ok lowered)
    (planned : Wrap.methodPlan lowered className method = .ok plan) :
    methodEntryPlan program className method = .ok plan := by
  simp only [methodEntryPlan, classes, bind, Except.bind]
  exact planned

structure MethodEntryCertificate {source : String} (wrapper : WrapperCertificate source)
    (className methodName : String) where
  class_ : Class
  classLookup : wrapper.original.program.classes.find? (·.name == className) = some class_
  classNamed : class_.name = className
  method : Ariadne.Function
  methodLookup : class_.methods.find? (·.name == methodName) = some method
  methodNamed : method.name = methodName
  plan : List ArgumentCheck
  planned : methodEntryPlan wrapper.original.program className method = .ok plan

/-- The receiver's actual class selects the certified method wrapper. -/
def WrappedSourceMethodInvokes (source wrapperText className methodName : String)
    (before : State) (address : Nat) (args : List Value) (value : Value) (after : State) : Prop :=
  ∃ wrapper : WrapperCertificate source, wrapper.text = wrapperText ∧
    ∃ entry : MethodEntryCertificate wrapper className methodName,
      (∃ fields, before.heap[address]? = some (.instance_ className fields)) ∧
      GuardedMethodInvokes wrapper.original.program entry.plan before address methodName args value after

/-- Lift actual method adequacy through a certified guard, without assuming
input-disjointness or evaluation of the whole wrapped method. -/
theorem MethodEntryCertificate.transfer {source : String} {wrapper : WrapperCertificate source}
    {className methodName : String} (entry : MethodEntryCertificate wrapper className methodName)
    {before after : State} {address : Nat} {args : List Value} {value : Value}
    (receiver : ∃ fields, before.heap[address]? = some (.instance_ className fields))
    (original : SourceInvokes source before (.method address methodName) args value after)
    (safe : entrySafe wrapper.original.program entry.plan before.heap (.ref address :: args) = true) :
    WrappedSourceMethodInvokes source wrapper.text className methodName before address args value after := by
  obtain ⟨program, checked, invoked⟩ := original
  have same : program = wrapper.original.program :=
    Except.ok.inj (checked.symm.trans wrapper.original.checked)
  subst program
  exact ⟨wrapper, rfl, entry, receiver, guarded_method_invokes_iff.mpr ⟨safe, invoked⟩⟩

end Ariadne.Ownership

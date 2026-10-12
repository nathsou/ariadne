import Ariadne.Ownership.Wrap

namespace Ariadne.Ownership

/-- Source and wrapper text are bound together by a kernel-checked renderer
equation. The wrapper shares the original checked implementation program. -/
structure WrapperCertificate (source : String) where
  original : Certificate source
  text : String
  emitted : Wrap.emit source original.program = .ok text

structure EntryCertificate {source : String} (wrapper : WrapperCertificate source) (name : String) where
  function : Ariadne.Function
  lookup : wrapper.original.program.functions.find? (fun f => f.name == name) = some function
  named : function.name = name
  exported : function.exported = true
  plan : List ArgumentCheck
  planned : entryPlan wrapper.original.program function = .ok plan

def WrappedSourceReturnsFrom (source wrapperText name : String) (heap : Heap)
    (args : List Value) (value : Value) : Prop :=
  ∃ wrapper : WrapperCertificate source, wrapper.text = wrapperText ∧
    ∃ entry : EntryCertificate wrapper name, ∃ after,
      GuardedInvokes wrapper.original.program entry.plan {heap} name args value after

/-- Lift the implementation's proved source behavior through its operational
entry guard. This rule composes with adequacy; it does not replace it. -/
theorem EntryCertificate.transfer {source : String} {wrapper : WrapperCertificate source}
    {name : String} (entry : EntryCertificate wrapper name) {heap : Heap} {args : List Value}
    {value : Value} (original : SourceReturnsFrom source name heap args value)
    (safe : entrySafe wrapper.original.program entry.plan heap args = true) :
    WrappedSourceReturnsFrom source wrapper.text name heap args value := by
  obtain ⟨after, program, checked, invoked⟩ := original
  have same : program = wrapper.original.program :=
    Except.ok.inj (checked.symm.trans wrapper.original.checked)
  subst program
  exact ⟨wrapper, rfl, entry, after, guarded_invokes_iff.mpr ⟨safe, invoked⟩⟩

end Ariadne.Ownership

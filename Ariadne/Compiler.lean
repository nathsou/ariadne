import Ariadne.OpenCompiler

namespace Ariadne.Compile

/-- Retain the original call-free API as a specialization of the open compiler. -/
def expression (p : Program) (budget : Nat) (e : Expr) : Checked (Expression p e) :=
  (Open.expression p false budget e).map fun f => ⟨f.code (apply p), f.correct, f.text⟩

def statement (p : Program) (budget : Nat) (s : Stmt) : Checked (Command p s) :=
  (Open.statement p false budget s).map fun f => ⟨f.code (apply p), f.correct, f.text⟩

def block (p : Program) (budget : Nat) (ss : List Stmt) : Checked (Block p ss) :=
  (Open.block p false budget ss).map fun f => ⟨f.code (apply p), f.correct, f.text⟩

/-- Compile one entry point. Other functions in the source may use the larger
operational subset; only the selected entry must fit this backend. -/
def function (p : Program) (name : String) :
    Checked (Fragment (Nat → List Value → Result Value) (fun fuel args => run p name fuel args)) := do
  match found : p.functions.find? (fun f => f.name == name) with
  | none => throw { code := "A4103", message := s!"Unknown compiler entry point '{name}'" }
  | some f =>
    for param in f.params do
      if Check.referenceType (← Check.resolve 100 p param.ty) then
        throw (unsupported param.span "reference parameters")
    if Check.referenceType (← Check.resolve 100 p f.result) then
      throw (unsupported f.span "reference results")
    let body ← statement p 256 f.body
    return {
      code := fun fuel args => (Target.function f.params body.code fuel {} args).map Prod.fst
      correct := by
        rw [body.correct]
        funext fuel args
        cases fuel with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => simp [Target.function, run, runState, apply, found, callBody]
          | succ n => simp [Target.function, run, runState, apply, found, callBody]
      text := "(fun fuel args => (Target.function (" ++ reprStr f.params ++ ") " ++
        body.text ++ " fuel {} args).map Prod.fst)" }

/-- Every successful compilation preserves all budgets, inputs, runtime errors,
and results. No frontend soundness assumption is needed for this equality. -/
theorem function_correct {p : Program} {name : String}
    {code : Nat → List Value → Result Value}
    (checked : (function p name).map Fragment.code = .ok code) :
    code = (fun fuel args => run p name fuel args) := by
  cases h : function p name with
  | error e => simp [h, Except.map] at checked
  | ok compiled =>
    simp only [h, Except.map, Except.ok.injEq] at checked
    exact checked.symm.trans compiled.correct

end Ariadne.Compile

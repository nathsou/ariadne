import Ariadne.Compiler

namespace Ariadne.Target

structure Definition where
  name : String
  params : List Param
  body : Runtime → Command

/-- Link all named functions through a decreasing recursion depth. The separate
runtime fuel is preserved exactly; it is not reset when entering a callee.

`external` retains model compatibility for reference-valued callables. Scalar
programs do not allocate closures or collection receivers. Removing this residual
branch requires a heap-shape theorem, rather than a claim based on testing. -/
def link (external : Runtime) (definitions : List Definition) : Nat → Runtime
  | 0 => fun _ _ _ _ => .error .timeout
  | depth + 1 => fun fuel s fn args => do
    match fuel with
    | 0 => throw .timeout
    | n + 1 =>
      match fn with
      | .function name =>
        match definitions.find? (fun f => f.name == name) with
        | some f => function f.params (f.body (link external definitions depth)) (n + 1) s args
        | none => return (← invokeScalar name args, s)
      | .stringMethod units name => return (← invokeString units name args, s)
      | _ => external (n + 1) s fn args

end Ariadne.Target

namespace Ariadne.Compile

/-- The lookup certificate binds names, parameter lists, and open bodies. -/
structure TableFor (p : Program) (functions : List Function) where
  definitions : List Target.Definition
  correct : ∀ name,
    ((definitions.find? (fun f => f.name == name)).map fun f => (f.params, f.body (apply p))) =
    ((functions.find? (fun f => f.name == name)).map fun f =>
      (f.params, fun fuel s => exec p fuel s f.body))
  causal : ∀ f ∈ definitions, Target.Causal f.body
  texts : List String

abbrev Table (p : Program) := TableFor p p.functions

/-- A linked runtime agrees with the source whenever its recursion depth covers
the execution budget. The theorem includes mutual recursion and failing runs. -/
theorem link_correct (p : Program) (table : Table p) (depth : Nat) :
    Target.Agree depth (Target.link (apply p) table.definitions depth) (apply p) := by
  induction depth with
  | zero =>
    intro fuel le
    have : fuel = 0 := by omega
    subst fuel
    funext s fn args
    rfl
  | succ depth ih =>
    intro fuel le
    funext s fn args
    cases fuel with
    | zero => rfl
    | succ n =>
      cases fn with
      | function name =>
        have correspondence := table.correct name
        cases ht : table.definitions.find? (fun f => f.name == name) with
        | none =>
          have sourceNone : p.functions.find? (fun f => f.name == name) = none := by
            cases hs : p.functions.find? (fun f => f.name == name) with
            | none => rfl
            | some f => simp [ht, hs] at correspondence
          simp [Target.link, apply, ht, sourceNone]
        | some f =>
          have member := List.mem_of_find?_eq_some ht
          have bodies := f.body
          have same := table.causal f member depth _ _ ih
          cases hs : p.functions.find? (fun f => f.name == name) with
          | none => simp [ht, hs] at correspondence
          | some source =>
            simp only [ht, hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at correspondence
            rcases correspondence with ⟨params, body⟩
            have frame := Target.function_congr (ps := f.params) same (fuel := n + 1) (by omega)
            simp only [Target.link, ht]
            rw [congrFun (congrFun frame s) args, params, body]
            cases n <;> simp [Target.function, apply, hs, callBody]
      | stringMethod units name => simp [Target.link, apply]
      | _ => rfl

private def scalarSignature (p : Program) (f : Function) : Checked Unit := do
  for param in f.params do
    if Check.referenceType (← Check.resolve 100 p param.ty) then
      throw (unsupported param.span "reference parameters")
  if Check.referenceType (← Check.resolve 100 p f.result) then
    throw (unsupported f.span "reference results")

private def inFunction (name : String) (result : Checked α) : Checked α :=
  result.mapError fun diagnostic => { diagnostic with
    notes := diagnostic.notes ++ [s!"While linking function '{name}'; every function in a linked unit must fit the scalar backend."] }

/-- Compile the whole scalar unit, so forward references and recursion require
neither source-order restrictions nor runtime source-body interpretation. -/
def definitions (p : Program) : (fs : List Function) → Checked (TableFor p fs)
  | [] => .ok {
      definitions := []
      correct := by intro name; rfl
      causal := by intro f h; cases h
      texts := [] }
  | f :: fs => do
    inFunction f.name (scalarSignature p f)
    let body ← inFunction f.name (Open.statement p true 256 f.body)
    let rest ← definitions p fs
    let target : Target.Definition := ⟨f.name, f.params, body.code⟩
    return {
      definitions := target :: rest.definitions
      correct := by
        intro name
        simp only [List.find?_cons, target]
        split
        · simp only [Option.map_some, body.correct]
        · exact rest.correct name
      causal := by
        intro entry member
        cases member with
        | head => exact body.causal
        | tail _ h => exact rest.causal entry h
      texts := ("{ name := " ++ reprStr f.name ++ ", params := (" ++ reprStr f.params ++
        "), body := fun runtime =>\n  " ++ body.text.replace "\n" "\n  " ++ " }") :: rest.texts }

/-- The closed recursive compiler preserves the same public result type as the
call-free compiler. Its proof covers every fuel and input value list. -/
def linkedFunction (p : Program) (name : String) :
    Checked (Fragment (Nat → List Value → Result Value) (fun fuel args => run p name fuel args)) := do
  if !(p.functions.any fun f => f.name == name) then
    throw { code := "A4103", message := s!"Unknown compiler entry point '{name}'" }
  let table ← definitions p p.functions
  return {
    code := fun fuel args =>
      (Target.link (apply p) table.definitions fuel fuel {} (.function name) args).map Prod.fst
    correct := by
      funext fuel args
      rw [link_correct p table fuel fuel (Nat.le_refl _)]
      rfl
    text := "(fun fuel args => (Target.link (apply program) [\n  " ++
      String.intercalate ",\n  " (table.texts.map fun text => text.replace "\n" "\n  ") ++
      "] fuel fuel {} (.function " ++ reprStr name ++ ") args).map Prod.fst)" }

/-- Keep small call-free artifacts stable. If calls require linking, every
function in the unit must belong to the scalar compiler fragment. -/
def entry (p : Program) (name : String) :
    Checked (Fragment (Nat → List Value → Result Value) (fun fuel args => run p name fuel args)) :=
  match function p name with
  | .ok compiled => .ok compiled
  | .error _ => linkedFunction p name

theorem entry_correct {p : Program} {name : String}
    {code : Nat → List Value → Result Value}
    (checked : (entry p name).map Fragment.code = .ok code) :
    code = (fun fuel args => run p name fuel args) := by
  cases h : entry p name with
  | error e => simp [h, Except.map] at checked
  | ok compiled =>
    simp only [h, Except.map, Except.ok.injEq] at checked
    exact checked.symm.trans compiled.correct

end Ariadne.Compile

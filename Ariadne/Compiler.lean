import Ariadne.Target
import Ariadne.Fuel
import Ariadne.Check

namespace Ariadne.Compile

/-- Proof-carrying compilation. Rendering is untrusted and is checked separately
against `code`; the preservation proof is part of every successful result. -/
structure Fragment (α : Type) (meaning : α) where
  code : α
  correct : code = meaning
  text : String

abbrev Expression (p : Program) (e : Expr) :=
  Fragment Target.Expression (fun fuel s => evalExpr p fuel s e)
abbrev Command (p : Program) (s : Stmt) :=
  Fragment Target.Command (fun fuel state => exec p fuel state s)
abbrev Block (p : Program) (ss : List Stmt) :=
  Fragment Target.Command (fun fuel state => execBlock p fuel state ss)

private def app (name : String) (args : List String) : String :=
  "(Target." ++ name ++ String.join (args.map (" " ++ ·)) ++ ")"

/-- Indent nested target commands; expressions remain compact. -/
private def commandApp (name : String) (args : List String) : String :=
  "(Target." ++ name ++ String.join (args.map fun arg =>
    "\n  " ++ arg.replace "\n" "\n  ") ++ ")"

private def unsupported (span : Span) (what : String) : Diagnostic :=
  { code := "A4101", span, message := s!"Scalar compilation does not yet support {what}",
    help := some "Use translate/certify for the operational model, or extract a function in the scalar compiler subset." }

private def exhausted (span : Span) : Diagnostic :=
  { code := "A4102", span, message := "Scalar compiler nesting budget exhausted",
    help := some "Split deeply nested expressions or blocks into smaller pieces." }

theorem loop_correct (p : Program) (guard : Expr) (body : Stmt) (update : Option Stmt) :
    Target.loop (fun n s => evalExpr p n s guard) (fun n s => exec p n s body)
      (update.map fun stmt n s => exec p n s stmt) =
    (fun n s => Ariadne.loop p n s guard body update) := by
  funext n s
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Target.loop, Ariadne.loop]
    cases update <;> simp only [Option.map] at ih ⊢ <;> simp only [ih]

/-- Compilation fuel is a frontend nesting limit, independent of runtime fuel. -/
def expression (p : Program) : (budget : Nat) → (e : Expr) → Checked (Expression p e)
  | 0, e => .error (exhausted e.span)
  | _ + 1, .literal v span => .ok {
      code := Target.literal v
      correct := by funext fuel s; cases fuel <;> rfl
      text := app "literal" [s!"({reprStr v})"] }
  | _ + 1, .var name span => .ok {
      code := Target.read name
      correct := by funext fuel s; cases fuel <;> rfl
      text := app "read" [reprStr name] }
  | n + 1, .unary op arg span => do
    let a ← expression p n arg
    return {
      code := Target.unary op a.code
      correct := by rw [a.correct]; funext fuel s; cases fuel <;> rfl
      text := app "unary" [reprStr op, a.text] }
  | n + 1, .binary op left right span => do
    let a ← expression p n left
    let b ← expression p n right
    return {
      code := Target.binary op a.code b.code
      correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
      text := app "binary" [reprStr op, a.text, b.text] }
  | n + 1, .conditional guard yes no span => do
    let c ← expression p n guard
    let a ← expression p n yes
    let b ← expression p n no
    return {
      code := Target.conditional c.code a.code b.code
      correct := by
        rw [c.correct, a.correct, b.correct]
        funext fuel s
        cases fuel with
        | zero => rfl
        | succ n => 
          simp only [Target.conditional, evalExpr]
          congr 1
          funext pair
          split <;> rfl
      text := app "conditional" [c.text, a.text, b.text] }
  | n + 1, .member object field span => do
    let a ← expression p n object
    return {
      code := Target.member a.code field
      correct := by rw [a.correct]; funext fuel s; cases fuel <;> rfl
      text := app "member" [a.text, reprStr field] }
  | n + 1, .index object offset span => do
    let a ← expression p n object
    let b ← expression p n offset
    return {
      code := Target.index a.code b.code
      correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
      text := app "index" [a.text, b.text] }
  | _ + 1, e@(.call ..) => .error (unsupported e.span "function or method calls")
  | _ + 1, e@(.array ..) => .error (unsupported e.span "array allocation")
  | _ + 1, e@(.record ..) => .error (unsupported e.span "record allocation")
  | _ + 1, e@(.newMap ..) => .error (unsupported e.span "Map allocation")
  | _ + 1, e@(.lambda ..) => .error (unsupported e.span "callbacks")

mutual
  def statement (p : Program) : (budget : Nat) → (s : Stmt) → Checked (Command p s)
    | 0, s => .error (exhausted s.span)
    | n + 1, .block ss span => do
      let b ← block p n ss
      return {
        code := Target.scope b.code
        correct := by rw [b.correct]; funext fuel s; cases fuel <;> rfl
        text := commandApp "scope" [b.text] }
    | n + 1, .let_ mutable name ty value span => do
      let v ← expression p n value
      return {
        code := Target.declare name v.code
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        text := commandApp "declare" [reprStr name, v.text] }
    | n + 1, .assign (.var name nameSpan) value span => do
      let v ← expression p n value
      return {
        code := Target.assign name v.code
        correct := by
          rw [v.correct]; funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases h : evalExpr p n s value <;>
                simp [Target.assign, exec, assignTarget, h, bind, Except.bind]
        text := commandApp "assign" [reprStr name, v.text] }
    | _ + 1, .assign target _ _ => .error (unsupported target.span "writes through references")
    | n + 1, .expr value span => do
      let v ← expression p n value
      return {
        code := Target.discard v.code
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        text := commandApp "discard" [v.text] }
    | n + 1, .if_ guard yes no span => do
      let c ← expression p n guard
      let a ← statement p n yes
      let b ← statement p n no
      return {
        code := Target.branch c.code a.code b.code
        correct := by
          rw [c.correct, a.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n => 
            simp only [Target.branch, exec]
            congr 1
            funext pair
            split <;> rfl
        text := commandApp "branch" [c.text, a.text, b.text] }
    | n + 1, .while_ guard body span => do
      let c ← expression p n guard
      let b ← statement p n body
      return {
        code := Target.while_ c.code b.code
        correct := by
          rw [c.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n => exact congrFun (congrFun (loop_correct p guard body none) n) s
        text := commandApp "while_" [c.text, b.text] }
    | n + 1, .for_ init guard update body span => do
      let i ← statement p n init
      let c ← expression p n guard
      let u ← statement p n update
      let b ← statement p n body
      return {
        code := Target.for_ i.code c.code u.code b.code
        correct := by
          rw [i.correct, c.correct, u.correct, b.correct]
          funext fuel s
          cases fuel with
          | zero => rfl
          | succ n =>
            simp only [Target.for_, exec]
            have h := loop_correct p guard body (some update)
            simp only [Option.map] at h
            rw [h]
        text := commandApp "for_" [i.text, c.text, u.text, b.text] }
    | n + 1, .return_ value span => do
      let v ← expression p n value
      return {
        code := Target.return_ v.code
        correct := by rw [v.correct]; funext fuel s; cases fuel <;> rfl
        text := commandApp "return_" [v.text] }
    | _ + 1, .break_ span => .ok {
        code := Target.break_
        correct := by funext fuel s; cases fuel <;> rfl
        text := "Target.break_" }
    | _ + 1, .continue_ span => .ok {
        code := Target.continue_
        correct := by funext fuel s; cases fuel <;> rfl
        text := "Target.continue_" }

  def block (p : Program) : (budget : Nat) → (ss : List Stmt) → Checked (Block p ss)
    | 0, ss => .error (exhausted ((ss.head?.map Stmt.span).getD {}))
    | _ + 1, [] => .ok {
        code := Target.empty
        correct := by funext fuel s; cases fuel <;> rfl
        text := "Target.empty" }
    | n + 1, first :: rest => do
      let a ← statement p n first
      let b ← block p n rest
      return {
        code := Target.sequence a.code b.code
        correct := by rw [a.correct, b.correct]; funext fuel s; cases fuel <;> rfl
        text := commandApp "sequence" [a.text, b.text] }
end

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

import Ariadne.Shallow.Adequacy.GuardedStatements
import Ariadne.Shallow.Adequacy.Joins
import Ariadne.Shallow.Safety.Structural

namespace Ariadne.Shallow.Adequacy
open Core

/-- Local bindings and scalar observations; the safety premise is separate. -/
structure GuardedFacts (program : Program) (names : Names Γ) (state : State)
    (env : Core.Env Γ interp) (model : Safety.Environment Γ interp) : Prop where
  related : Environment names state env
  valid : state.ValidBindings
  values : Safety.ScalarEnvironment model env
  free : MathFree program state

abbrev GuardedPre (interp : Named.Interp) (Γ : List Core.Ty) :=
  State → Core.Env Γ interp → Safety.Environment Γ interp → Prop

/-- A normal exit carries the actual captured model and its continuation guard.
The suffix certificate itself is shared and is proved independently. -/
def GuardedResume {interp : Named.Interp} (pre : GuardedPre interp Δ)
    (continuation : Term Δ t) (state : State) (value : t.denote interp) : Prop :=
  ∃ captured model, pre state captured model ∧
    value = Denote.term continuation captured ∧ (Safety.term continuation model).2 = true

/-- Syntax certificates for guarded scalar joins. Every safety premise is the
existing Core safety interpreter; no constructor assumes source execution. -/
inductive GuardedJoins (program : Program) (interp : Named.Interp) :
    {Γ : List Core.Ty} → {t : Core.Ty} → Scalar t → GuardedPre interp Γ →
    (State → t.denote interp → Prop) → List Stmt → Term Γ t → Prop where
  | exit {scalar : Scalar t} {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
      (term : Term Γ t)
      (resume : ∀ state env model, pre state env model → (Safety.term term model).2 = true →
        post state (Denote.term term env)) :
      GuardedJoins program interp scalar pre post [] term
  | resume {scalar : Scalar t} {pre : GuardedPre interp Γ} {suffixPre : GuardedPre interp Δ}
      {post : State → t.denote interp → Prop} {leading suffix : List Stmt}
      {term : Term Γ t} {continuation : Term Δ t}
      (branches : GuardedJoins program interp scalar pre (GuardedResume suffixPre continuation) leading term)
      (next : GuardedJoins program interp scalar suffixPre post suffix continuation) :
      GuardedJoins program interp scalar pre post (leading ++ suffix) term
  | emptyBlock {scalar : Scalar t} {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
      {rest : List Stmt} {term : Term Γ t}
      (next : GuardedJoins program interp scalar pre post rest term) (span : Span) :
      GuardedJoins program interp scalar pre post (.block [] span :: rest) term
  | appendStopped {scalar : Scalar t} {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
      {leading : List Stmt} {term : Term Γ t}
      (body : GuardedJoins program interp scalar pre (fun _ _ => False) leading term) (rest : List Stmt) :
      GuardedJoins program interp scalar pre post (leading ++ rest) term
  | consequence {scalar : Scalar t} {pre pre' : GuardedPre interp Γ}
      {post post' : State → t.denote interp → Prop} {statements : List Stmt} {term : Term Γ t}
      (strengthen : ∀ state env model, pre' state env model → pre state env model)
      (weaken : ∀ state value, post state value → post' state value)
      (body : GuardedJoins program interp scalar pre post statements term) :
      GuardedJoins program interp scalar pre' post' statements term
  | return_ {scalar : Scalar t} {names : Names Γ} {pre : GuardedPre interp Γ}
      {post : State → t.denote interp → Prop} {expression : Expr} {term : Term Γ t}
      (input : GuardedScalarExpr names scalar expression term)
      (facts : ∀ state env model, pre state env model → GuardedFacts program names state env model)
      (span : Span) (rest : List Stmt) :
      GuardedJoins program interp scalar pre post (.return_ expression span :: rest) term
  | let_ {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
      {pre : GuardedPre interp Γ} {nextPre : GuardedPre interp (a :: Γ)}
      {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
      {body : Term (a :: Γ) t} {rest : List Stmt}
      (name : String) (input : GuardedScalarExpr names repr expression value)
      (facts : ∀ state env model, pre state env model → GuardedFacts program names state env model)
      (step : ∀ state env model, pre state env model → nextPre
        (state.declare name (repr.encode (Denote.term value env))) (Denote.term value env, env)
        ((Safety.term value model).1, model))
      (next : GuardedJoins program interp scalar nextPre post rest body)
      (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
      GuardedJoins program interp scalar pre post (.let_ mutable name annotation expression span :: rest)
        (.let_ name value body)
  | assign {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
      {pre : GuardedPre interp Γ} {nextPre : GuardedPre interp (a :: Γ)}
      {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
      {body : Term (a :: Γ) t} {rest : List Stmt}
      (target : Var Γ a) (visible : names.visible target = true)
      (input : GuardedScalarExpr names repr expression value)
      (facts : ∀ state env model, pre state env model → GuardedFacts program names state env model)
      (step : ∀ state env model, pre state env model → ∀ address, state.Binds (names.get target) address → nextPre
        {state with heap := state.heap.set address (.cell (repr.encode (Denote.term value env)))}
        (Denote.term value env, env) ((Safety.term value model).1, model))
      (next : GuardedJoins program interp scalar nextPre post rest body) (targetSpan span : Span) :
      GuardedJoins program interp scalar pre post (.assign (.var (names.get target) targetSpan) expression span :: rest)
        (.let_ (names.get target) value body)
  | if_ {scalar : Scalar t} {names : Names Γ} {pre : GuardedPre interp Γ}
      {post : State → t.denote interp → Prop} {condition : Expr} {test : Term Γ .bool}
      {yes no : Stmt} {rest : List Stmt} {a b : Term Γ t}
      (input : GuardedScalarExpr names .bool condition test)
      (facts : ∀ state env model, pre state env model → GuardedFacts program names state env model)
      (yesBody : GuardedJoins program interp scalar pre post (yes :: rest) a)
      (noBody : GuardedJoins program interp scalar pre post (no :: rest) b) (span : Span) :
      GuardedJoins program interp scalar pre post (.if_ condition yes no span :: rest) (.ite test a b)
  | block {scalar : Scalar t} {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
      {statements : List Stmt} {term : Term Γ t}
      (body : ∀ saved : Ariadne.Env,
        GuardedJoins program interp scalar (fun state env model => pre state env model ∧ state.env = saved)
          (fun after value => post {after with env := saved} value) statements term) (span : Span) :
      GuardedJoins program interp scalar pre post [.block statements span] term
  | bindJoin {scalar : Scalar t} {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
      {continuation : Term Δ t} {body : Term (.fn (environmentType Δ) t :: Γ) t} {statements : List Stmt}
      (branch : GuardedJoins program interp scalar
        (fun state extended modeled => ∃ env model, pre state env model ∧
          extended = (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env) ∧
          modeled = ((Safety.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) model).1, model))
        post statements body) :
      GuardedJoins program interp scalar pre post statements (.let_ "join" continuation.abstract body)

private theorem letSafe {interp : Named.Interp} {value : Term Γ a} {body : Term (a :: Γ) t}
    {model : Safety.Environment Γ interp} {name : String}
    (safe : (Safety.term (.let_ name value body) model).2 = true) :
    (Safety.term value model).2 = true ∧ (Safety.term body ((Safety.term value model).1, model)).2 = true := by
  simpa only [Safety.term, Bool.and_eq_true] using safe

/-- Structural soundness in the original statement evaluator. -/
theorem GuardedJoins.sound {program : Program} {interp : Named.Interp} {scalar : Scalar t}
    {pre : GuardedPre interp Γ} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (translation : GuardedJoins program interp scalar pre post statements term)
    (state : State) (env : Core.Env Γ interp) (model : Safety.Environment Γ interp)
    (h : pre state env model) (safe : (Safety.term term model).2 = true) :
    ∃ out, ExecutesBlock program state statements out ∧ JoinOutcome scalar post (Denote.term term env) out := by
  induction translation generalizing state with
  | exit term resume => exact ⟨{state}, ExecutesBlock.nil program state, Or.inr ⟨rfl, resume state env model h safe⟩⟩
  | resume branches next ihb ihn =>
    obtain ⟨middle, executed, returned | normal⟩ := ihb state env model h safe
    · exact ⟨middle, executed.append_stopped (by rw [returned.1]; decide) _, Or.inl returned⟩
    · obtain ⟨captured, capturedModel, related, equal, guarded⟩ := normal.2
      obtain ⟨out, run, finalResult⟩ := ihn middle.state captured capturedModel related guarded
      exact ⟨out, executesBlock_append_normal executed normal.1 run, equal ▸ finalResult⟩
  | emptyBlock next span ih =>
    obtain ⟨out, run, result⟩ := ih state env model h safe
    exact ⟨out, ExecutesBlock.next (ExecutesStatement.block (ExecutesBlock.nil program state) span) rfl run, result⟩
  | appendStopped body rest ih =>
    obtain ⟨out, run, returned | impossible⟩ := ih state env model h safe
    · exact ⟨out, run.append_stopped (by rw [returned.1]; decide) rest, Or.inl returned⟩
    · exact False.elim impossible.2
  | consequence strengthen weaken body ih =>
    obtain ⟨out, run, returned | normal⟩ := ih state env model (strengthen state env model h) safe
    · exact ⟨out, run, Or.inl returned⟩
    · exact ⟨out, run, Or.inr ⟨normal.1, weaken _ _ normal.2⟩⟩
  | return_ input facts span rest =>
    have f := facts state env model h
    exact ⟨_, ExecutesBlock.stop (ExecutesStatement.return_ (input.sound program interp state env model f.related f.values f.free safe) span)
      rest (by intro h; cases h), Or.inl ⟨rfl, rfl⟩⟩
  | let_ name input facts step next mutable annotation span ih =>
    have f := facts state env model h
    have parts := letSafe safe
    obtain ⟨out, executed, result⟩ := ih _ _ _ (step state env model h) parts.2
    exact ⟨out, ExecutesBlock.next (ExecutesStatement.let_
      (input.sound program interp state env model f.related f.values f.free parts.1) mutable name annotation span) rfl executed, result⟩
  | @assign t a Γ scalar repr names pre nextPre post expression value body rest target visible input facts step next targetSpan span ih =>
    have f := facts state env model h
    have parts := letSafe safe
    obtain ⟨address, bound, _⟩ := State.lookup_binds (f.related target repr visible)
    obtain ⟨out, executed, result⟩ := ih _ _ _ (step state env model h address bound) parts.2
    exact ⟨out, ExecutesBlock.next (assign_expression
      (input.sound program interp state env model f.related f.values f.free parts.1)
      bound (f.valid.allocated bound) targetSpan span) rfl executed, result⟩
  | @if_ t Γ scalar names pre post condition test yes no rest a b input facts yesBody noBody span ihy ihn =>
    have f := facts state env model h
    have testValue : (Safety.term test model).1 = Denote.term test env := input.scalarCore.value model env f.values
    have parts : (Safety.term test model).2 = true ∧
        (if Denote.term test env then Safety.term a model else Safety.term b model).2 = true := by
      simpa only [Safety.term, testValue, Bool.and_eq_true] using safe
    cases value : Denote.term test env
    · obtain ⟨out, executed, result⟩ := ihn state env model h (by simpa [value] using parts.2)
      refine ⟨out, ?_, ?_⟩
      · apply ExecutesBlock.if_ (input.sound program interp state env model f.related f.values f.free parts.1) (span := span)
        simpa [Scalar.encode, Value.truthy, value] using executed
      · simpa [Denote.term, value] using result
    · obtain ⟨out, executed, result⟩ := ihy state env model h (by simpa [value] using parts.2)
      refine ⟨out, ?_, ?_⟩
      · apply ExecutesBlock.if_ (input.sound program interp state env model f.related f.values f.free parts.1) (span := span)
        simpa [Scalar.encode, Value.truthy, value] using executed
      · simpa [Denote.term, value] using result
  | block body span ih =>
    obtain ⟨out, executed, returned | normal⟩ := ih state.env state env model ⟨h, rfl⟩ safe
    · exact ⟨{out with state := {out.state with env := state.env}},
        ExecutesBlock.stop (ExecutesStatement.block executed span) [] (by rw [returned.1]; decide), Or.inl returned⟩
    · exact ⟨{state := {out.state with env := state.env}},
        ExecutesBlock.next (ExecutesStatement.block executed span) normal.1 (ExecutesBlock.nil program _), Or.inr ⟨rfl, normal.2⟩⟩
  | bindJoin branch ih =>
    exact ih state _ _ ⟨env, model, h, rfl, rfl⟩ (letSafe safe).2

namespace GuardedJoins
variable {program : Program} {interp : Named.Interp}

theorem shared {scalar : Scalar t} {pre : GuardedPre interp Γ} {suffixPre : GuardedPre interp Δ}
    {post : State → t.denote interp → Prop} {leading suffix : List Stmt} {continuation : Term Δ t}
    {body : Term (.fn (environmentType Δ) t :: Γ) t}
    (next : GuardedJoins program interp scalar suffixPre post suffix continuation)
    (branches : GuardedJoins program interp scalar
      (fun state extended modeled => ∃ env model, pre state env model ∧
        extended = (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env) ∧
        modeled = ((Safety.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) model).1, model))
      (GuardedResume suffixPre continuation) leading body) :
    GuardedJoins program interp scalar pre post (leading ++ suffix) (.let_ "join" continuation.abstract body) :=
  .resume (.bindJoin branches) next

theorem returned {scalar : Scalar t} {pre : GuardedPre interp Γ}
    {statements : List Stmt} {term : Term Γ t}
    (proof : GuardedJoins program interp scalar pre (fun _ _ => False) statements term)
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (inputs : pre state env model) (safe : (Safety.term term model).2 = true) :
    ∃ after, ExecutesBlock program state statements
      { control := .returned, value := scalar.encode (Denote.term term env), state := after } := by
  obtain ⟨out, executed, result⟩ := proof.sound state env model inputs safe
  rcases result with ⟨control, value⟩ | ⟨_, impossible⟩
  · refine ⟨out.state, ?_⟩
    cases out
    simp_all
  · contradiction
end GuardedJoins

/-- Transfer consumes exactly the guard on the emitted Core body and initial
model; arbitrary mixed environments are allowed inside the structural proof. -/
theorem guarded_joins_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (scalar : Scalar t) (term : Term Γ t)
    (statements : List Stmt) (blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block statements blockSpan)
    (interp : Named.Interp) (pre : GuardedPre interp Γ)
    (translation : GuardedJoins certificate.program interp scalar pre (fun _ _ => False) statements term)
    (env : Core.Env Γ interp) (model : Safety.Environment Γ interp) (heap : Heap) (args : List Value)
    (inputs : pre (bindArguments { heap } function.params args) env model)
    (safe : (Safety.term term model).2 = true) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) := by
  obtain ⟨after, executed⟩ := translation.returned inputs safe
  apply certificate.transfer_from
  apply invoke_returned lookup
  rw [body]
  exact ExecutesStatement.block executed blockSpan

end Ariadne.Shallow.Adequacy

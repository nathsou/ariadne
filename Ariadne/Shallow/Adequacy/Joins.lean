import Ariadne.Shallow.Adequacy.Statements
import Ariadne.Shallow.Lemmas.Core

namespace Ariadne.Shallow.Adequacy
open Core

variable {interp : Named.Interp}

/-- The product used by the elaborator to pass captured locals to a shared join. -/
def packEnvironment : {Γ : List Core.Ty} → Core.Env Γ interp → (environmentType Γ).denote interp
  | [], _ => ()
  | _ :: _, (head, tail) => (head, packEnvironment tail)

@[simp] theorem denote_project (tuple : Term Δ (environmentType Γ)) (env : Core.Env Δ interp)
    (captured : Core.Env Γ interp) (equal : Denote.term tuple env = packEnvironment captured)
    (v : Var Γ t) : Denote.term (project tuple v) env = v.get captured := by
  induction v generalizing Δ with
  | here => exact congrArg Prod.fst equal
  | there v ih =>
    exact ih (.snd tuple) env captured.2 (congrArg Prod.snd equal)

/-- Native application of a closed shared continuation reconstructs its captured
Core environment. This theorem does not rewrite or duplicate the continuation. -/
theorem denote_abstract (body : Term Γ t) (env : Core.Env Δ interp) (captured : Core.Env Γ interp) :
    Denote.term (body.abstract : Term Δ (.fn (environmentType Γ) t)) env (packEnvironment captured) =
      Denote.term body captured := by
  simp only [Term.abstract, Denote.term, Denote.substitute]
  congr 1
  apply Core.Env.ext_lookup
  intro u v
  simp only [Core.Substitution.eval, Core.Var.get_ofLookup]
  exact denote_project (.var (.here : Var [environmentType Γ] (environmentType Γ)))
    ((packEnvironment captured, ()) : Core.Env [environmentType Γ] interp) captured rfl v

/-- A normal exit carries a ghost prediction of the shared continuation's value.
An actual source return already carries that value. The source machine remains
`execBlock`; only the postcondition is in continuation-passing form. -/
def JoinOutcome (scalar : Scalar t) (post : State → t.denote interp → Prop)
    (value : t.denote interp) (out : Completion) : Prop :=
  (out.control = .returned ∧ out.value = scalar.encode value) ∨
  (out.control = .normal ∧ post out.state value)

/-- A compositional proof judgment for a source leading and its actual Core term.
`pre` includes scalar bindings and any ghost specifications for join variables.
`post` is discharged when the source suffix is resumed. -/
def JoinFlow (program : Program) (scalar : Scalar t)
    (pre : State → Core.Env Γ interp → Prop) (post : State → t.denote interp → Prop)
    (statements : List Stmt) (term : Term Γ t) : Prop :=
  ∀ state env, pre state env → ∃ out, ExecutesBlock program state statements out ∧
    JoinOutcome scalar post (Denote.term term env) out

/-- Normal execution composes with a suffix in the original fuel evaluator. -/
theorem executesBlock_append_normal {program : Program} {before : State} {leading : List Stmt}
    {middle out : Completion} (first : ExecutesBlock program before leading middle)
    (normal : middle.control = .normal) {suffix : List Stmt}
    (next : ExecutesBlock program middle.state suffix out) :
    ExecutesBlock program before (leading ++ suffix) out := by
  induction leading generalizing before with
  | nil =>
    obtain ⟨_, fuel, run⟩ := first
    cases fuel with
    | zero => cases run
    | succ fuel =>
      have equal : ({state := before} : Completion) = middle := by
        simpa [execBlock, pure, Except.pure] using run
      cases equal
      exact next
  | cons statement statements ih =>
    obtain ⟨head, run, stopped | continued⟩ := first.cons_inv
    · exact False.elim (stopped.1 (stopped.2 ▸ normal))
    · exact ExecutesBlock.next run continued.1 (ih continued.2)

namespace JoinFlow

/-- A continuation application is a normal source exit, not a source call to an
invented `#join` function. Its ghost specification is the only premise here. -/
theorem jump {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    (fn : Term Γ (.fn a t)) (argument : Term Γ a)
    (resume : ∀ state env, pre state env → post state (Denote.term fn env (Denote.term argument env))) :
    JoinFlow program scalar pre post [] (.app fn argument) := by
  intro state env h
  exact ⟨{ state }, ExecutesBlock.nil program state, Or.inr ⟨rfl, resume state env h⟩⟩

theorem return_ {program : Program} {scalar : Scalar t} {names : Names Γ}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    {expression : Expr} {term : Term Γ t}
    (input : ScalarExpr names scalar expression term)
    (related : ∀ state env, pre state env → Environment names state env)
    (span : Span) (rest : List Stmt) :
    JoinFlow program scalar pre post (.return_ expression span :: rest) term := by
  intro state env h
  exact ⟨_, ExecutesBlock.stop (ExecutesStatement.return_ (input.sound program interp state env (related state env h)) span)
    rest (by intro h; cases h), Or.inl ⟨rfl, rfl⟩⟩

theorem let_ {program : Program} {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
    {pre : State → Core.Env Γ interp → Prop} {nextPre : State → Core.Env (a :: Γ) interp → Prop}
    {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
    {body : Term (a :: Γ) t} {rest : List Stmt}
    (name : String) (input : ScalarExpr names repr expression value)
    (related : ∀ state env, pre state env → Environment names state env)
    (step : ∀ state env, pre state env → nextPre
      (state.declare name (repr.encode (Denote.term value env))) (Denote.term value env, env))
    (next : JoinFlow program scalar nextPre post rest body)
    (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
    JoinFlow program scalar pre post (.let_ mutable name annotation expression span :: rest) (.let_ name value body) := by
  intro state env h
  obtain ⟨out, executed, result⟩ := next _ _ (step state env h)
  exact ⟨out, ExecutesBlock.next (ExecutesStatement.let_ (input.sound program interp state env (related state env h))
    mutable name annotation span) rfl executed, result⟩

theorem assign {program : Program} {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
    {pre : State → Core.Env Γ interp → Prop} {nextPre : State → Core.Env (a :: Γ) interp → Prop}
    {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
    {body : Term (a :: Γ) t} {rest : List Stmt}
    (target : Var Γ a) (visible : names.visible target = true)
    (input : ScalarExpr names repr expression value)
    (related : ∀ state env, pre state env → Environment names state env ∧ state.ValidBindings)
    (step : ∀ state env, pre state env → ∀ address, state.Binds (names.get target) address → nextPre
      {state with heap := state.heap.set address (.cell (repr.encode (Denote.term value env)))}
      (Denote.term value env, env))
    (next : JoinFlow program scalar nextPre post rest body) (targetSpan span : Span) :
    JoinFlow program scalar pre post (.assign (.var (names.get target) targetSpan) expression span :: rest)
      (.let_ (names.get target) value body) := by
  intro state env h
  have facts := related state env h
  obtain ⟨address, bound, _⟩ := State.lookup_binds (facts.1 target repr visible)
  obtain ⟨out, executed, result⟩ := next _ _ (step state env h address bound)
  exact ⟨out, ExecutesBlock.next
    (assign_expression (input.sound program interp state env facts.1) bound (facts.2.allocated bound) targetSpan span)
    rfl executed, result⟩

theorem if_ {program : Program} {scalar : Scalar t} {names : Names Γ}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    {condition : Expr} {test : Term Γ .bool} {yes no : Stmt} {rest : List Stmt} {a b : Term Γ t}
    (input : ScalarExpr names .bool condition test)
    (related : ∀ state env, pre state env → Environment names state env)
    (yesBody : JoinFlow program scalar pre post (yes :: rest) a)
    (noBody : JoinFlow program scalar pre post (no :: rest) b) (span : Span) :
    JoinFlow program scalar pre post (.if_ condition yes no span :: rest) (.ite test a b) := by
  intro state env h
  cases value : Denote.term test env
  · obtain ⟨out, executed, result⟩ := noBody state env h
    refine ⟨out, ?_, ?_⟩
    · apply ExecutesBlock.if_ (input.sound program interp state env (related state env h)) (span := span)
      simpa [Scalar.encode, Value.truthy, value] using executed
    · simpa [Denote.term, value] using result
  · obtain ⟨out, executed, result⟩ := yesBody state env h
    refine ⟨out, ?_, ?_⟩
    · apply ExecutesBlock.if_ (input.sound program interp state env (related state env h)) (span := span)
      simpa [Scalar.encode, Value.truthy, value] using executed
    · simpa [Denote.term, value] using result

/-- Lexical scope restores the original binding environment but retains heap
writes. The continuation specification therefore observes the restored scope. -/
theorem block {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ∀ saved : Ariadne.Env,
      JoinFlow program scalar (fun state env => pre state env ∧ state.env = saved)
        (fun after value => post {after with env := saved} value) statements term) (span : Span) :
    JoinFlow program scalar pre post [.block statements span] term := by
  intro state env h
  obtain ⟨out, executed, result⟩ := body state.env state env ⟨h, rfl⟩
  rcases result with returned | normal
  · exact ⟨{out with state := {out.state with env := state.env}},
      ExecutesBlock.stop (ExecutesStatement.block executed span) [] (by rw [returned.1]; decide),
      Or.inl returned⟩
  · exact ⟨{state := {out.state with env := state.env}},
      ExecutesBlock.next (ExecutesStatement.block executed span) normal.1 (ExecutesBlock.nil program _),
      Or.inr ⟨rfl, normal.2⟩⟩

/-- A closed continuation binding is a ghost step in the source. The function
remains a single native Core let-bound value. -/
theorem bindJoin {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    {continuation : Term Δ t} {body : Term (.fn (environmentType Δ) t :: Γ) t}
    {statements : List Stmt}
    (branch : JoinFlow program scalar
      (fun state extended => ∃ env, pre state env ∧
        extended = (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env))
      post statements body) :
    JoinFlow program scalar pre post statements (.let_ "join" continuation.abstract body) := by
  intro state env h
  exact branch state _ ⟨env, h, rfl⟩

/-- Existing scalar suffix witnesses embed without changing their Core terms. -/
theorem scalarStatements {program : Program} {scalar : Scalar t} {names : Names Γ}
    {statements : List Stmt} {term : Term Γ t}
    (translation : ScalarStatements names scalar statements term) :
    JoinFlow (interp := interp) program scalar
      (fun state env => Environment names state env ∧ state.ValidBindings)
      (fun _ _ => False) statements term := by
  intro state env h
  obtain ⟨after, executed⟩ := translation.sound program interp state env h.1 h.2
  exact ⟨_, executed, Or.inl ⟨rfl, rfl⟩⟩

/-- Discharge each normal exit with one separately proved suffix. The witness
for that suffix occurs once, independently of how many branches reach it. -/
theorem resume {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {suffixPre : State → Core.Env Δ interp → Prop}
    {post : State → t.denote interp → Prop}
    {leading suffix : List Stmt} {term : Term Γ t} {continuation : Term Δ t}
    (branches : JoinFlow program scalar pre
      (fun state value => ∃ captured, suffixPre state captured ∧ value = Denote.term continuation captured)
      leading term)
    (next : JoinFlow program scalar suffixPre post suffix continuation) :
    JoinFlow program scalar pre post (leading ++ suffix) term := by
  intro state env h
  obtain ⟨middle, executed, result⟩ := branches state env h
  rcases result with returned | normal
  · exact ⟨middle, executed.append_stopped (by rw [returned.1]; decide) suffix, Or.inl returned⟩
  · obtain ⟨captured, related, equal⟩ := normal.2
    obtain ⟨out, run, finalResult⟩ := next middle.state captured related
    refine ⟨out, executesBlock_append_normal executed normal.1 run, ?_⟩
    simpa only [equal] using finalResult

/-- The elaborator's shared-join shape: certify the suffix once, then certify
branches with a ghost prediction of its value. Native `let` and `app` remain in
the actual Core body; no beta-inlining of branch continuations is required. -/
theorem shared {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {suffixPre : State → Core.Env Δ interp → Prop}
    {post : State → t.denote interp → Prop}
    {leading suffix : List Stmt} {continuation : Term Δ t}
    {body : Term (.fn (environmentType Δ) t :: Γ) t}
    (next : JoinFlow program scalar suffixPre post suffix continuation)
    (branches : JoinFlow program scalar
      (fun state extended => ∃ env, pre state env ∧
        extended = (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env))
      (fun state value => ∃ captured, suffixPre state captured ∧ value = Denote.term continuation captured)
      leading body) :
    JoinFlow program scalar pre post (leading ++ suffix)
      (.let_ "join" continuation.abstract body) :=
  resume (bindJoin branches) next

/-- Close the CPS proof to ordinary operational return convergence. -/
theorem returned {program : Program} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {statements : List Stmt} {term : Term Γ t}
    (proof : JoinFlow program scalar pre (fun _ _ => False) statements term)
    {state : State} {env : Core.Env Γ interp} (inputs : pre state env) :
    ∃ after, ExecutesBlock program state statements
      { control := .returned, value := scalar.encode (Denote.term term env), state := after } := by
  obtain ⟨out, executed, result⟩ := proof state env inputs
  rcases result with ⟨control, value⟩ | ⟨_, impossible⟩
  · refine ⟨out.state, ?_⟩
    cases out
    simp_all
  · contradiction

end JoinFlow

/-- Source transfer for shared continuations, with arbitrary starting heaps.
Its premise is assembled using the local `JoinFlow` rules above. -/
theorem join_flow_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (scalar : Scalar t) (term : Term Γ t)
    (statements : List Stmt) (blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block statements blockSpan)
    (interp : Named.Interp) (pre : State → Core.Env Γ interp → Prop)
    (translation : JoinFlow certificate.program scalar pre (fun _ _ => False) statements term)
    (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : pre (bindArguments { heap } function.params args) env) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) := by
  obtain ⟨after, executed⟩ := translation.returned inputs
  apply certificate.transfer_from
  apply invoke_returned lookup
  rw [body]
  exact ExecutesStatement.block executed blockSpan


end Ariadne.Shallow.Adequacy

namespace Ariadne.Shallow.Adequacy
open Core
variable {interp : Named.Interp}

/-- A generated function binder has no corresponding source binding. -/
theorem Environment.join {names : Names Γ} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (name : String) (value : (Core.Ty.fn a b).denote interp) :
    Environment (names.cons name) state (value, env) := by
  intro t v scalar visible
  cases v with
  | here => cases scalar
  | there v =>
    have facts : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
    exact related v scalar facts.1

/-- Allocating a local and restoring the old scope preserves all old lookups. -/
theorem lookup_restore_declare {state : State} {query : String} {result : Value}
    (found : state.lookup query = .ok result) (name : String) (value : Value) :
    ({state.declare name value with env := state.env} : State).lookup query = .ok result := by
  obtain ⟨address, bound, stored⟩ := State.lookup_binds found
  have allocated := (List.getElem?_eq_some_iff.mp stored).choose
  change state.env.find? (fun entry => entry.1 == query) = some (query, address) at bound
  simp [State.lookup, State.declare, State.alloc, bound, List.getElem?_append_left allocated,
    stored, pure, Except.pure]

theorem Environment.restore_declare {names : Names Γ} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (name : String) (value : Value) :
    Environment names {state.declare name value with env := state.env} env := by
  intro t v scalar visible
  exact lookup_restore_declare (related v scalar visible) name value

theorem validBindings_restore_declare {state : State} (valid : state.ValidBindings)
    (name : String) (value : Value) :
    ({state.declare name value with env := state.env} : State).ValidBindings := by
  constructor
  · intro query address bound
    have := valid.allocated bound
    simp only [State.declare, State.alloc, List.length_append, List.length_cons, List.length_nil]
    omega
  · exact valid.separate

end Ariadne.Shallow.Adequacy

namespace Ariadne.Shallow.Adequacy
open Core

/-- Syntax-directed certificates for scalar control flow with shared native
continuations. The premises concern expressions, scalar binding relations, and
local ghost invariants. No constructor assumes execution of a whole function. -/
inductive ScalarJoins (interp : Named.Interp) :
    {Γ : List Core.Ty} → {t : Core.Ty} → Scalar t →
    (State → Core.Env Γ interp → Prop) → (State → t.denote interp → Prop) →
    List Stmt → Term Γ t → Prop where
  | exit {scalar : Scalar t} {pre : State → Core.Env Γ interp → Prop}
      {post : State → t.denote interp → Prop} (term : Term Γ t)
      (resume : ∀ state env, pre state env → post state (Denote.term term env)) :
      ScalarJoins interp scalar pre post [] term
  | resume {scalar : Scalar t}
      {pre : State → Core.Env Γ interp → Prop} {suffixPre : State → Core.Env Δ interp → Prop}
      {post : State → t.denote interp → Prop}
      {leading suffix : List Stmt} {term : Term Γ t} {continuation : Term Δ t}
      (branches : ScalarJoins interp scalar pre
        (fun state value => ∃ captured, suffixPre state captured ∧ value = Denote.term continuation captured)
        leading term)
      (next : ScalarJoins interp scalar suffixPre post suffix continuation) :
      ScalarJoins interp scalar pre post (leading ++ suffix) term
  | emptyBlock {scalar : Scalar t}
      {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
      {rest : List Stmt} {term : Term Γ t}
      (next : ScalarJoins interp scalar pre post rest term) (span : Span) :
      ScalarJoins interp scalar pre post (.block [] span :: rest) term
  | appendStopped {scalar : Scalar t}
      {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
      {leading : List Stmt} {term : Term Γ t}
      (body : ScalarJoins interp scalar pre (fun _ _ => False) leading term) (rest : List Stmt) :
      ScalarJoins interp scalar pre post (leading ++ rest) term
  | consequence {scalar : Scalar t}
      {pre pre' : State → Core.Env Γ interp → Prop}
      {post post' : State → t.denote interp → Prop}
      {statements : List Stmt} {term : Term Γ t}
      (strengthen : ∀ state env, pre' state env → pre state env)
      (weaken : ∀ state value, post state value → post' state value)
      (body : ScalarJoins interp scalar pre post statements term) :
      ScalarJoins interp scalar pre' post' statements term
  | jump {scalar : Scalar t} {pre : State → Core.Env Γ interp → Prop}
      {post : State → t.denote interp → Prop}
      (fn : Term Γ (.fn a t)) (argument : Term Γ a)
      (resume : ∀ state env, pre state env → post state (Denote.term fn env (Denote.term argument env))) :
      ScalarJoins interp scalar pre post [] (.app fn argument)
  | return_ {scalar : Scalar t} {names : Names Γ}
      {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
      {expression : Expr} {term : Term Γ t}
      (input : ScalarExpr names scalar expression term)
      (related : ∀ state env, pre state env → Environment names state env)
      (span : Span) (rest : List Stmt) :
      ScalarJoins interp scalar pre post (.return_ expression span :: rest) term
  | let_ {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
      {pre : State → Core.Env Γ interp → Prop} {nextPre : State → Core.Env (a :: Γ) interp → Prop}
      {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
      {body : Term (a :: Γ) t} {rest : List Stmt}
      (name : String) (input : ScalarExpr names repr expression value)
      (related : ∀ state env, pre state env → Environment names state env)
      (step : ∀ state env, pre state env → nextPre
        (state.declare name (repr.encode (Denote.term value env))) (Denote.term value env, env))
      (next : ScalarJoins interp scalar nextPre post rest body)
      (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
      ScalarJoins interp scalar pre post (.let_ mutable name annotation expression span :: rest) (.let_ name value body)
  | assign {scalar : Scalar t} {repr : Scalar a} {names : Names Γ}
      {pre : State → Core.Env Γ interp → Prop} {nextPre : State → Core.Env (a :: Γ) interp → Prop}
      {post : State → t.denote interp → Prop} {expression : Expr} {value : Term Γ a}
      {body : Term (a :: Γ) t} {rest : List Stmt}
      (target : Var Γ a) (visible : names.visible target = true)
      (input : ScalarExpr names repr expression value)
      (related : ∀ state env, pre state env → Environment names state env ∧ state.ValidBindings)
      (step : ∀ state env, pre state env → ∀ address, state.Binds (names.get target) address → nextPre
        {state with heap := state.heap.set address (.cell (repr.encode (Denote.term value env)))}
        (Denote.term value env, env))
      (next : ScalarJoins interp scalar nextPre post rest body) (targetSpan span : Span) :
      ScalarJoins interp scalar pre post (.assign (.var (names.get target) targetSpan) expression span :: rest)
        (.let_ (names.get target) value body)
  | if_ {scalar : Scalar t} {names : Names Γ}
      {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
      {condition : Expr} {test : Term Γ .bool} {yes no : Stmt} {rest : List Stmt} {a b : Term Γ t}
      (input : ScalarExpr names .bool condition test)
      (related : ∀ state env, pre state env → Environment names state env)
      (yesBody : ScalarJoins interp scalar pre post (yes :: rest) a)
      (noBody : ScalarJoins interp scalar pre post (no :: rest) b) (span : Span) :
      ScalarJoins interp scalar pre post (.if_ condition yes no span :: rest) (.ite test a b)
  | block {scalar : Scalar t}
      {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
      {statements : List Stmt} {term : Term Γ t}
      (body : ∀ saved : Ariadne.Env,
        ScalarJoins interp scalar (fun state env => pre state env ∧ state.env = saved)
          (fun after value => post {after with env := saved} value) statements term) (span : Span) :
      ScalarJoins interp scalar pre post [.block statements span] term
  | scalarStatements {scalar : Scalar t} {names : Names Γ}
      {statements : List Stmt} {term : Term Γ t}
      (translation : ScalarStatements names scalar statements term) :
      ScalarJoins interp scalar (fun state env => Environment names state env ∧ state.ValidBindings)
        (fun _ _ => False) statements term
  | shared {scalar : Scalar t}
      {pre : State → Core.Env Γ interp → Prop} {suffixPre : State → Core.Env Δ interp → Prop}
      {post : State → t.denote interp → Prop}
      {leading suffix : List Stmt} {continuation : Term Δ t}
      {body : Term (.fn (environmentType Δ) t :: Γ) t}
      (next : ScalarJoins interp scalar suffixPre post suffix continuation)
      (branches : ScalarJoins interp scalar
        (fun state extended => ∃ env, pre state env ∧
          extended = (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env))
        (fun state value => ∃ captured, suffixPre state captured ∧ value = Denote.term continuation captured)
        leading body) :
      ScalarJoins interp scalar pre post (leading ++ suffix)
        (.let_ "join" continuation.abstract body)

/-- Structural soundness against `execBlock`/`Fuel.Converges`. Shared suffix
certificates are induction hypotheses, never execution assumptions. -/
theorem ScalarJoins.sound {interp : Named.Interp} {scalar : Scalar t}
    {pre : State → Core.Env Γ interp → Prop} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (translation : ScalarJoins interp scalar pre post statements term) (program : Program) :
    JoinFlow program scalar pre post statements term := by
  induction translation with
  | exit term resume =>
    intro state env h
    exact ⟨{state}, ExecutesBlock.nil program state, Or.inr ⟨rfl, resume state env h⟩⟩
  | resume branches next ihb ihn => exact JoinFlow.resume ihb ihn
  | emptyBlock next span ih =>
    intro state env h
    obtain ⟨out, run, result⟩ := ih state env h
    exact ⟨out, ExecutesBlock.next (ExecutesStatement.block (ExecutesBlock.nil program state) span) rfl run, result⟩
  | appendStopped body rest ih =>
    intro state env h
    obtain ⟨out, run, returned | impossible⟩ := ih state env h
    · exact ⟨out, run.append_stopped (by rw [returned.1]; decide) rest, Or.inl returned⟩
    · exact False.elim impossible.2
  | consequence strengthen weaken body ih =>
    intro state env h
    obtain ⟨out, run, returned | normal⟩ := ih state env (strengthen state env h)
    · exact ⟨out, run, Or.inl returned⟩
    · exact ⟨out, run, Or.inr ⟨normal.1, weaken _ _ normal.2⟩⟩
  | jump fn argument resume => exact JoinFlow.jump fn argument resume
  | return_ input related span rest => exact JoinFlow.return_ input related span rest
  | let_ name input related step next mutable annotation span ih =>
    exact JoinFlow.let_ name input related step ih mutable annotation span
  | assign target visible input related step next targetSpan span ih =>
    exact JoinFlow.assign target visible input related step ih targetSpan span
  | if_ input related yesBody noBody span ihy ihn => exact JoinFlow.if_ input related ihy ihn span
  | block body span ih => exact JoinFlow.block ih span
  | scalarStatements translation => exact JoinFlow.scalarStatements translation
  | shared next branches ihn ihb => exact JoinFlow.shared ihn ihb

/-- Source transfer from a compositional syntax certificate, including shared
joins and non-returning lexical scopes, for arbitrary starting heaps. -/
theorem scalar_joins_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (scalar : Scalar t) (term : Term Γ t)
    (statements : List Stmt) (blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block statements blockSpan)
    (interp : Named.Interp) (pre : State → Core.Env Γ interp → Prop)
    (translation : ScalarJoins interp scalar pre (fun _ _ => False) statements term)
    (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : pre (bindArguments { heap } function.params args) env) :
    SourceReturnsFrom source function.name heap args (scalar.encode (Denote.term term env)) :=
  join_flow_source certificate function scalar term statements blockSpan lookup body interp pre
    (translation.sound certificate.program) env heap args inputs

end Ariadne.Shallow.Adequacy

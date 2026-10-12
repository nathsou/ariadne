import Ariadne.Shallow.Adequacy.GuardedJoins
import Ariadne.Shallow.Adequacy.JoinsContext

namespace Ariadne.Shallow.Adequacy
open Core

namespace Ghosts
/-- The same finite ghost table describes the guarded function interpreter.
Unlike native denotation, its function values retain invocation guards. -/
def Modeled {interp : Named.Interp} (ghosts : Ghosts Γ) (model : Safety.Environment Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t) (value : Term [] t), ghosts v = some value →
    Safety.getVariable v model = (Safety.term value ()).1

theorem Modeled.skip {interp : Named.Interp} {ghosts : Ghosts Γ} {model : Safety.Environment Γ interp}
    (h : Modeled ghosts model) (value : Safety.Model a interp) : Modeled ghosts.skip (value, model) := by
  intro t v term found
  cases v with
  | here => cases found
  | there v => exact h v term found

theorem Modeled.bind {interp : Named.Interp} {ghosts : Ghosts Γ} {model : Safety.Environment Γ interp}
    (h : Modeled ghosts model) (term : Term [] a) : Modeled (ghosts.bind term) ((Safety.term term ()).1, model) := by
  intro t v value found
  cases v with
  | here => cases Option.some.inj found; rfl
  | there v => exact h v value found
end Ghosts

/-- Canonical local invariant for guarded joins and lexical scopes. Both models
of every known closed join are tracked, even through scalar SSA binders. -/
structure GuardedJoinContext (program : Program) {interp : Named.Interp}
    (names : Names Γ) (ghosts : Ghosts Γ) (active : List String) (frames : List ScopeFrame)
    (state : State) (env : Core.Env Γ interp) (model : Safety.Environment Γ interp) : Prop where
  native : JoinContext names ghosts active frames state env
  values : Safety.ScalarEnvironment model env
  modeled : ghosts.Modeled model
  free : MathFree program state
  savedFree : ∀ frame ∈ frames, frame.saved.any (fun p => p.1 == "Math") = false

namespace GuardedJoinContext
variable {program : Program} {interp : Named.Interp}

theorem facts {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active frames state env model) :
    GuardedFacts program names state env model := ⟨h.native.related, h.native.valid, h.values, h.free⟩

theorem declare {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active frames state env model)
    (name : String) (repr : Scalar a) (value : a.denote interp) (modeled : Safety.Model a interp)
    (equal : Safety.scalarValue repr modeled = value) (unshadow : name ≠ "Math")
    (fresh : ∀ frame ∈ frames, name ∉ frame.names) :
    GuardedJoinContext program (names.cons name) ghosts.skip (name :: active) frames
      (state.declare name (repr.encode value)) (value, env) (modeled, model) :=
  ⟨h.native.declare name repr value fresh, Safety.ScalarEnvironment.cons h.values repr modeled value equal,
    Ghosts.Modeled.skip h.modeled modeled, h.free.declare name unshadow _, h.savedFree⟩

theorem assign {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active frames state env model)
    (name : String) (repr : Scalar a) (value : a.denote interp) (modeled : Safety.Model a interp)
    (equal : Safety.scalarValue repr modeled = value) (address : Nat) (bound : state.Binds name address) :
    GuardedJoinContext program (names.cons name) ghosts.skip active frames
      {state with heap := state.heap.set address (.cell (repr.encode value))} (value, env) (modeled, model) :=
  ⟨h.native.assign name repr value address bound, Safety.ScalarEnvironment.cons h.values repr modeled value equal,
    Ghosts.Modeled.skip h.modeled modeled, h.free.withHeap _, h.savedFree⟩

theorem bindJoin {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active frames state env model)
    (name : String) (continuation : Term Δ t) :
    GuardedJoinContext program (names.cons name) (ghosts.bind continuation.abstract) active frames state
      (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env)
      ((Safety.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) model).1, model) := by
  refine ⟨h.native.bindJoin name continuation, ?_, Ghosts.Modeled.bind h.modeled continuation.abstract, h.free, h.savedFree⟩
  intro u v repr
  cases v with
  | here => cases repr
  | there v => exact h.values v repr

theorem openScope {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active frames state env model) (saved : Ariadne.Env) (equal : state.env = saved) :
    GuardedJoinContext program names ghosts active ({names := active, saved} :: frames) state env model := by
  refine ⟨h.native.openScope saved equal, h.values, h.modeled, h.free, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact equal ▸ h.free.unbound
  · exact h.savedFree frame member

theorem capture {fromNames : Names Γ} {fromGhosts : Ghosts Γ} {toNames : Names Δ} {toGhosts : Ghosts Δ}
    {select : Renaming Δ Γ} (capture : Captures fromNames fromGhosts toNames toGhosts select)
    {active : List String} {frames : List ScopeFrame} {state : State} {env : Core.Env Γ interp}
    {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program fromNames fromGhosts active frames state env model) :
    GuardedJoinContext program toNames toGhosts active frames state (select.pull env) (Safety.Environment.pull select model) := by
  refine ⟨h.native.capture capture, ?_, ?_, h.free, h.savedFree⟩
  · intro t v repr
    rw [Safety.Environment.get_pull]
    simpa [Core.Renaming.pull] using h.values (select v) repr
  · intro t v term found
    rw [Safety.Environment.get_pull]
    exact h.modeled (select v) term (capture.ghosts v term found)

theorem restore {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frame : ScopeFrame} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} {model : Safety.Environment Γ interp}
    (h : GuardedJoinContext program names ghosts active (frame :: frames) state env model)
    (outside : ∀ {t} (v : Var Γ t) (_repr : Scalar t), names.visible v = true → names.get v ∈ frame.names) :
    GuardedJoinContext program names ghosts frame.names frames {state with env := frame.saved} env model := by
  refine ⟨h.native.restore outside, h.values, h.modeled, ?_, ?_⟩
  · exact ⟨h.savedFree frame (by simp), h.free.abs, h.free.floor, h.free.trunc⟩
  · intro f member; exact h.savedFree f (List.mem_cons_of_mem _ member)

theorem initial {names : Names Γ} {active : List String} {state : State} {env : Core.Env Γ interp}
    {model : Safety.Environment Γ interp} (related : Environment names state env) (valid : state.ValidBindings)
    (shape : state.env.map Prod.fst = active) (values : Safety.ScalarEnvironment model env) (free : MathFree program state) :
    GuardedJoinContext program names Ghosts.empty active [] state env model :=
  ⟨JoinContext.initial related valid shape, values, (by intro t v value impossible; cases impossible), free,
    (by intro frame impossible; cases impossible)⟩
end GuardedJoinContext

/-- Variable capture tuples are pure in the guarded model, including function
components. Their function values retain the original invocation guards. -/
theorem safety_captureTuple {interp : Named.Interp} (select : Renaming Δ Γ) (model : Safety.Environment Γ interp) :
    Safety.term (captureTuple Δ select) model = (Safety.packEnvironment (Safety.Environment.pull select model), true) := by
  induction Δ with
  | nil => rfl
  | cons t Δ ih =>
    simp only [captureTuple, Safety.term, ih]
    rfl

namespace GuardedJoins
variable {program : Program} {interp : Named.Interp}

theorem contextReturn {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {term : Term Γ t} (input : GuardedScalarExpr names scalar expression term)
    (span : Span) (rest : List Stmt) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (.return_ expression span :: rest) term :=
  .return_ input (fun _ _ _ h => h.facts) span rest

theorem contextLet {scalar : Scalar t} {repr : Scalar a} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
    (name : String) (unshadow : name ≠ "Math") (input : GuardedScalarExpr names repr expression value)
    (fresh : ∀ frame ∈ frames, name ∉ frame.names)
    (next : GuardedJoins program interp scalar (GuardedJoinContext program (names.cons name) ghosts.skip (name :: active) frames) post rest body)
    (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post
      (.let_ mutable name annotation expression span :: rest) (.let_ name value body) :=
  .let_ name input (fun _ _ _ h => h.facts)
    (fun _ env model h => h.declare name repr _ _ (input.scalarCore.value model env h.values) unshadow fresh)
    next mutable annotation span

theorem contextAssign {scalar : Scalar t} {repr : Scalar a} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
    (target : Var Γ a) (visible : names.visible target = true) (input : GuardedScalarExpr names repr expression value)
    (next : GuardedJoins program interp scalar (GuardedJoinContext program (names.cons (names.get target)) ghosts.skip active frames) post rest body)
    (targetSpan span : Span) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post
      (.assign (.var (names.get target) targetSpan) expression span :: rest) (.let_ (names.get target) value body) :=
  .assign target visible input (fun _ _ _ h => h.facts)
    (fun _ env model h address bound => h.assign (names.get target) repr _ _ (input.scalarCore.value model env h.values) address bound)
    next targetSpan span

theorem contextIf {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {condition : Expr} {test : Term Γ .bool} {yes no : Stmt} {rest : List Stmt} {a b : Term Γ t}
    (input : GuardedScalarExpr names .bool condition test)
    (yesBody : GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (yes :: rest) a)
    (noBody : GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (no :: rest) b) (span : Span) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (.if_ condition yes no span :: rest) (.ite test a b) :=
  .if_ input (fun _ _ _ h => h.facts) yesBody noBody span

theorem contextBlock {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ∀ saved : Ariadne.Env,
      GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active ({names := active, saved} :: frames))
        (fun after value => post {after with env := saved} value) statements term) (span : Span) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post [.block statements span] term :=
  .block (fun saved => .consequence (fun _ _ _ h => h.1.openScope saved h.2) (fun _ _ h => h) (body saved)) span

theorem contextStoppedBlock {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ∀ saved : Ariadne.Env,
      GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active ({names := active, saved} :: frames))
        (fun _ _ => False) statements term) (span : Span) (rest : List Stmt) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (.block statements span :: rest) term :=
  .appendStopped (contextBlock body span) rest

theorem contextShared {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {suffixPre : GuardedPre interp Δ} {leading suffix : List Stmt} {continuation : Term Δ t}
    {body : Term (.fn (environmentType Δ) t :: Γ) t}
    (joinName : String) (next : GuardedJoins program interp scalar suffixPre post suffix continuation)
    (branches : GuardedJoins program interp scalar
      (GuardedJoinContext program (names.cons joinName) (ghosts.bind continuation.abstract) active frames)
      (GuardedResume suffixPre continuation) leading body) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames) post (leading ++ suffix)
      (.let_ "join" continuation.abstract body) := by
  apply GuardedJoins.shared next
  apply GuardedJoins.consequence (body := branches) (weaken := fun _ _ h => h)
  intro state extended modeled h
  obtain ⟨env, model, h, rfl, rfl⟩ := h
  exact h.bindJoin joinName continuation

/-- At a real native jump, the actual application guard is transported through
the closed abstraction and the captured variable tuple. There is no separately
assumed suffix guard. -/
theorem contextJump {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame}
    {suffixPre : GuardedPre interp Δ} {continuation : Term Δ t}
    (fn : Var Γ (.fn (environmentType Δ) t)) (known : ghosts fn = some continuation.abstract)
    (select : Renaming Δ Γ) (finish : State → State)
    (adapt : ∀ state env model, GuardedJoinContext program names ghosts active frames state env model →
      suffixPre (finish state) (select.pull env) (Safety.Environment.pull select model)) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames)
      (fun state value => GuardedResume suffixPre continuation (finish state) value)
      [] (.app (.var fn) (captureTuple Δ select)) := by
  apply GuardedJoins.exit
  intro state env model h safe
  refine ⟨select.pull env, Safety.Environment.pull select model, adapt state env model h, ?_, ?_⟩
  · change fn.get env (Denote.term (captureTuple Δ select) env) = _
    rw [h.native.known fn continuation.abstract known, denote_captureTuple]
    exact denote_abstract (Δ := []) continuation () (select.pull env)
  · have call := h.modeled fn continuation.abstract known
    simpa only [Safety.term, safety_captureTuple, call, Bool.true_and,
      Safety.term_abstract_apply] using safe

theorem contextInlineExit {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {suffixPre : GuardedPre interp Δ}
    {continuation : Term Δ t} {term : Term Γ t}
    (select : Renaming Δ Γ) (equal : term = continuation.rename select) (finish : State → State)
    (adapt : ∀ state env model, GuardedJoinContext program names ghosts active frames state env model →
      suffixPre (finish state) (select.pull env) (Safety.Environment.pull select model)) :
    GuardedJoins program interp scalar (GuardedJoinContext program names ghosts active frames)
      (fun state value => GuardedResume suffixPre continuation (finish state) value) [] term := by
  apply GuardedJoins.exit
  intro state env model h safe
  exact ⟨select.pull env, Safety.Environment.pull select model, adapt state env model h,
    by rw [equal, Denote.rename], by simpa only [equal, Safety.term_rename] using safe⟩
end GuardedJoins
end Ariadne.Shallow.Adequacy

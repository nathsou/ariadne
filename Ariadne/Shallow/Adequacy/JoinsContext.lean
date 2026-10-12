import Ariadne.Shallow.Adequacy.Joins

namespace Ariadne.Shallow.Adequacy
open Core

/-- Discarded source locals can remain as unused Core parameters after a
flattened scope. Visibility records exactly the names still in lexical scope. -/
def Names.restrict (names : Names Γ) (active : List String) : Names Γ :=
  {get := names.get, visible := fun v => names.visible v && active.contains (names.get v)}

/-- A finite typed table of known closed values. Scalar SSA binders leave the
old table intact; generated join binders add their actual closed Core function. -/
abbrev Ghosts (Γ : List Core.Ty) := ∀ {t}, Var Γ t → Option (Term [] t)
namespace Ghosts

def empty : Ghosts Γ := fun _ => none

def skip (ghosts : Ghosts Γ) : Ghosts (a :: Γ)
  | _, .here => none
  | _, .there v => ghosts v

def bind (value : Term [] a) (ghosts : Ghosts Γ) : Ghosts (a :: Γ)
  | _, .here => some value
  | _, .there v => ghosts v

def Holds {interp : Named.Interp} (ghosts : Ghosts Γ) (env : Core.Env Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t) (value : Term [] t), ghosts v = some value → v.get env = Denote.term value ()

theorem Holds.skip {a : Core.Ty} {interp : Named.Interp} {ghosts : Ghosts Γ} {env : Core.Env Γ interp}
    (h : Holds ghosts env) (value : a.denote interp) : Holds ghosts.skip (value, env) := by
  intro t v term found
  cases v with
  | here => cases found
  | there v => exact h v term found

theorem Holds.bind {interp : Named.Interp} {ghosts : Ghosts Γ} {env : Core.Env Γ interp}
    (h : Holds ghosts env) (term : Term [] a) : Holds (ghosts.bind term) (Denote.term term (), env) := by
  intro t v value found
  cases v with
  | here => cases Option.some.inj found; rfl
  | there v => exact h v value found
end Ghosts

/-- Restoring a scope is sound when its visible names still denote the same
cells. Heap writes are deliberately absent from this environment-only relation. -/
def ExtendsBindings (saved active : Ariadne.Env) : Prop :=
  ∀ name address, saved.find? (fun entry => entry.1 == name) = some (name, address) →
    active.find? (fun entry => entry.1 == name) = some (name, address)

structure ScopeFrame where
  names : List String
  saved : Ariadne.Env

def ScopeFrames : List ScopeFrame → Ariadne.Env → Prop
  | [], _ => True
  | frame :: rest, active => frame.saved.map Prod.fst = frame.names ∧
      ExtendsBindings frame.saved active ∧ ScopeFrames rest frame.saved

theorem ScopeFrames.declare {frames : List ScopeFrame} {env : Ariadne.Env}
    (h : ScopeFrames frames env) (name : String) (address : Nat)
    (fresh : ∀ frame ∈ frames, name ∉ frame.names) :
    ScopeFrames frames ((name, address) :: env) := by
  cases frames with
  | nil => trivial
  | cons frame rest =>
    refine ⟨h.1, ?_, h.2.2⟩
    intro query loc bound
    have member : query ∈ frame.names := by
      rw [← h.1]
      exact List.mem_map.mpr ⟨(query, loc), List.mem_of_find?_eq_some bound, rfl⟩
    have different : name ≠ query := by intro equal; subst query; exact fresh frame (by simp) member
    simpa [List.find?_cons, different] using h.2.1 query loc bound

/-- The canonical precondition used by a proof printer. `active` tracks source
binding names (declarations only), while `names` also tracks scalar SSA versions.
All non-scalar ghost facts are equalities to actual closed Core values. -/
structure JoinContext {interp : Named.Interp} (names : Names Γ) (ghosts : Ghosts Γ)
    (active : List String) (frames : List ScopeFrame) (state : State) (env : Core.Env Γ interp) : Prop where
  related : Environment names state env
  valid : state.ValidBindings
  known : ghosts.Holds env
  activeNames : state.env.map Prod.fst = active
  scopes : ScopeFrames frames state.env

namespace JoinContext
variable {interp : Named.Interp}

theorem declare {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} (h : JoinContext names ghosts active frames state env)
    (name : String) (repr : Scalar a) (value : a.denote interp)
    (fresh : ∀ frame ∈ frames, name ∉ frame.names) :
    JoinContext (names.cons name) ghosts.skip (name :: active) frames
      (state.declare name (repr.encode value)) (value, env) :=
  ⟨Environment.declare h.related name repr value, h.valid.declare name _, Ghosts.Holds.skip h.known value,
    by simpa [State.declare, State.alloc] using congrArg (name :: ·) h.activeNames,
    h.scopes.declare name state.heap.length fresh⟩

theorem assign {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} (h : JoinContext names ghosts active frames state env)
    (name : String) (repr : Scalar a) (value : a.denote interp) (address : Nat)
    (bound : state.Binds name address) :
    JoinContext (names.cons name) ghosts.skip active frames
      {state with heap := state.heap.set address (.cell (repr.encode value))} (value, env) :=
  ⟨Environment.assign h.related h.valid name address bound repr value, h.valid.write address _,
    Ghosts.Holds.skip h.known value, h.activeNames, h.scopes⟩

theorem bindJoin {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} (h : JoinContext names ghosts active frames state env)
    (name : String) (continuation : Term Δ t) :
    JoinContext (names.cons name) (ghosts.bind continuation.abstract) active frames state
      (Denote.term (continuation.abstract : Term Γ (.fn (environmentType Δ) t)) env, env) :=
  ⟨Environment.join h.related name _, h.valid, Ghosts.Holds.bind h.known continuation.abstract, h.activeNames, h.scopes⟩

theorem openScope {names : Names Γ} {ghosts : Ghosts Γ} {active : List String} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp} (h : JoinContext names ghosts active frames state env)
    (saved : Ariadne.Env) (equal : state.env = saved) :
    JoinContext names ghosts active ({ names := active, saved } :: frames) state env := by
  subst saved
  exact ⟨h.related, h.valid, h.known, h.activeNames, h.activeNames, (fun _ _ h => h), h.scopes⟩

end JoinContext

/-- The exact variable tuple at a generated continuation call. -/
def captureTuple {Γ : List Core.Ty} : (Δ : List Core.Ty) → Renaming Δ Γ → Term Γ (environmentType Δ)
  | [], _ => .unit
  | _ :: Δ, select => .pair (.var (select .here)) (captureTuple Δ (fun v => select (.there v)))

theorem denote_captureTuple {interp : Named.Interp} (select : Renaming Δ Γ) (env : Core.Env Γ interp) :
    Denote.term (captureTuple Δ select) env = packEnvironment (select.pull env) := by
  induction Δ with
  | nil => rfl
  | cons t Δ ih =>
    dsimp [captureTuple, Denote.term, packEnvironment, Core.Renaming.pull, Core.Env.ofLookup]
    congr 1
    exact ih (fun v => select (.there v))

/-- Capture checks are finite facts about typed variables, visibility and names;
a printer can discharge them by cases and definitional reduction. -/
structure Captures (fromNames : Names Γ) (fromGhosts : Ghosts Γ)
    (toNames : Names Δ) (toGhosts : Ghosts Δ) (select : Renaming Δ Γ) : Prop where
  names : ∀ {t} (v : Var Δ t) (_repr : Scalar t), toNames.visible v = true →
    fromNames.visible (select v) = true ∧ fromNames.get (select v) = toNames.get v
  ghosts : ∀ {t} (v : Var Δ t) (value : Term [] t), toGhosts v = some value →
    fromGhosts (select v) = some value

theorem JoinContext.capture {interp : Named.Interp} {fromNames : Names Γ} {fromGhosts : Ghosts Γ}
    {toNames : Names Δ} {toGhosts : Ghosts Δ} {select : Renaming Δ Γ}
    (capture : Captures fromNames fromGhosts toNames toGhosts select)
    {active : List String} {frames : List ScopeFrame} {state : State} {env : Core.Env Γ interp}
    (h : JoinContext fromNames fromGhosts active frames state env) :
    JoinContext toNames toGhosts active frames state (select.pull env) := by
  refine ⟨?_, h.valid, ?_, h.activeNames, h.scopes⟩
  · intro t v repr visible
    have facts := capture.names v repr visible
    have found := h.related (select v) repr facts.1
    simpa [Core.Renaming.pull, facts.2] using found
  · intro t v term found
    simpa [Core.Renaming.pull] using h.known (select v) term (capture.ghosts v term found)

private theorem find_of_name_mem {env : Ariadne.Env} {name : String} (member : name ∈ env.map Prod.fst) :
    ∃ address, env.find? (fun entry => entry.1 == name) = some (name, address) := by
  induction env with
  | nil => simp at member
  | cons entry entries ih =>
    rcases entry with ⟨key, address⟩
    by_cases equal : key = name
    · subst key; exact ⟨address, by simp⟩
    · obtain ⟨loc, found⟩ := ih (by simpa [equal, Ne.symm equal] using member)
      exact ⟨loc, by simpa [equal] using found⟩

/-- A source block restores its saved names; scalar writes survive because both
scopes point at the same cells. The ghost context does not mention source cells. -/
theorem JoinContext.restore {interp : Named.Interp} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frame : ScopeFrame} {frames : List ScopeFrame}
    {state : State} {env : Core.Env Γ interp}
    (h : JoinContext names ghosts active (frame :: frames) state env)
    (outside : ∀ {t} (v : Var Γ t) (_repr : Scalar t), names.visible v = true → names.get v ∈ frame.names) :
    JoinContext names ghosts frame.names frames {state with env := frame.saved} env := by
  refine ⟨?_, ?_, h.known, h.scopes.1, h.scopes.2.2⟩
  · intro t v repr visible
    obtain ⟨address, bound⟩ := find_of_name_mem (h.scopes.1 ▸ outside v repr visible)
    have current := h.scopes.2.1 _ _ bound
    have related := h.related v repr visible
    simpa only [State.lookup, bound, current] using related
  · constructor
    · intro name address bound
      exact h.valid.allocated (h.scopes.2.1 name address bound)
    · intro left right address hl hr
      exact h.valid.separate (h.scopes.2.1 left address hl) (h.scopes.2.1 right address hr)

end Ariadne.Shallow.Adequacy

namespace Ariadne.Shallow.Adequacy
open Core
variable {interp : Named.Interp}

theorem JoinContext.initial {names : Names Γ} {active : List String} {state : State} {env : Core.Env Γ interp}
    (related : Environment names state env) (valid : state.ValidBindings)
    (shape : state.env.map Prod.fst = active) : JoinContext names Ghosts.empty active [] state env :=
  ⟨related, valid, (by intro t v value impossible; cases impossible), shape, trivial⟩

namespace ScalarJoins

theorem contextReturn {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {term : Term Γ t} (input : ScalarExpr names scalar expression term)
    (span : Span) (rest : List Stmt) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post (.return_ expression span :: rest) term :=
  .return_ input (fun _ _ h => h.related) span rest

theorem contextLet {scalar : Scalar t} {repr : Scalar a} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
    (name : String) (input : ScalarExpr names repr expression value)
    (fresh : ∀ frame ∈ frames, name ∉ frame.names)
    (next : ScalarJoins interp scalar (JoinContext (names.cons name) ghosts.skip (name :: active) frames) post rest body)
    (mutable : Bool) (annotation : Option Ariadne.Ty) (span : Span) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post
      (.let_ mutable name annotation expression span :: rest) (.let_ name value body) :=
  .let_ name input (fun _ _ h => h.related) (fun _ _ h => h.declare name repr _ fresh) next mutable annotation span

theorem contextAssign {scalar : Scalar t} {repr : Scalar a} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {expression : Expr} {value : Term Γ a} {body : Term (a :: Γ) t} {rest : List Stmt}
    (target : Var Γ a) (visible : names.visible target = true)
    (input : ScalarExpr names repr expression value)
    (next : ScalarJoins interp scalar (JoinContext (names.cons (names.get target)) ghosts.skip active frames) post rest body)
    (targetSpan span : Span) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post
      (.assign (.var (names.get target) targetSpan) expression span :: rest) (.let_ (names.get target) value body) :=
  .assign target visible input (fun _ _ h => ⟨h.related, h.valid⟩)
    (fun _ _ h address bound => h.assign (names.get target) repr _ address bound) next targetSpan span

theorem contextIf {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {condition : Expr} {test : Term Γ .bool} {yes no : Stmt} {rest : List Stmt} {a b : Term Γ t}
    (input : ScalarExpr names .bool condition test)
    (yesBody : ScalarJoins interp scalar (JoinContext names ghosts active frames) post (yes :: rest) a)
    (noBody : ScalarJoins interp scalar (JoinContext names ghosts active frames) post (no :: rest) b) (span : Span) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post
      (.if_ condition yes no span :: rest) (.ite test a b) :=
  .if_ input (fun _ _ h => h.related) yesBody noBody span

theorem contextBlock {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ∀ saved : Ariadne.Env,
      ScalarJoins interp scalar (JoinContext names ghosts active ({names := active, saved} :: frames))
        (fun after value => post {after with env := saved} value) statements term) (span : Span) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post [.block statements span] term :=
  .block (fun saved => .consequence (fun _ _ h => h.1.openScope saved h.2) (fun _ _ h => h) (body saved)) span

theorem contextStoppedBlock {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ∀ saved : Ariadne.Env,
      ScalarJoins interp scalar (JoinContext names ghosts active ({names := active, saved} :: frames))
        (fun _ _ => False) statements term) (span : Span) (rest : List Stmt) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post (.block statements span :: rest) term :=
  .appendStopped (contextBlock body span) rest

theorem contextScalar {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {statements : List Stmt} {term : Term Γ t}
    (body : ScalarStatements names scalar statements term) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post statements term :=
  .consequence (fun _ _ h => ⟨h.related, h.valid⟩) (fun _ _ h => False.elim h) (.scalarStatements body)

theorem contextShared {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame} {post : State → t.denote interp → Prop}
    {suffixPre : State → Core.Env Δ interp → Prop} {leading suffix : List Stmt} {continuation : Term Δ t}
    {body : Term (.fn (environmentType Δ) t :: Γ) t}
    (joinName : String) (next : ScalarJoins interp scalar suffixPre post suffix continuation)
    (branches : ScalarJoins interp scalar
      (JoinContext (names.cons joinName) (ghosts.bind continuation.abstract) active frames)
      (fun state value => ∃ captured, suffixPre state captured ∧ value = Denote.term continuation captured)
      leading body) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames) post (leading ++ suffix)
      (.let_ "join" continuation.abstract body) := by
  apply ScalarJoins.shared next
  apply ScalarJoins.consequence (body := branches) (weaken := fun _ _ h => h)
  intro state extended h
  obtain ⟨env, h, rfl⟩ := h
  exact h.bindJoin joinName continuation

/-- When the elaborator has already flattened a block, its scalar suffix is
related by renaming to the actual remaining Core term. This rule preserves that
existing term; it never substitutes or inlines a native shared continuation. -/
theorem contextInlineExit {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame}
    {suffixPre : State → Core.Env Δ interp → Prop} {continuation : Term Δ t} {term : Term Γ t}
    (select : Renaming Δ Γ) (equal : term = continuation.rename select) (finish : State → State)
    (adapt : ∀ state env, JoinContext names ghosts active frames state env → suffixPre (finish state) (select.pull env)) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames)
      (fun state value => ∃ captured, suffixPre (finish state) captured ∧ value = Denote.term continuation captured)
      [] term := by
  apply ScalarJoins.exit
  intro state env h
  exact ⟨select.pull env, adapt state env h, by rw [equal, Denote.rename]⟩

/-- A jump reads its function from the typed ghost table and its arguments from
an actual tuple of Core variables. `adapt` consists of capture/restore helpers;
it contains no operational execution premise. -/
theorem contextJump {scalar : Scalar t} {names : Names Γ} {ghosts : Ghosts Γ}
    {active : List String} {frames : List ScopeFrame}
    {suffixPre : State → Core.Env Δ interp → Prop} {continuation : Term Δ t}
    (fn : Var Γ (.fn (environmentType Δ) t)) (known : ghosts fn = some continuation.abstract)
    (select : Renaming Δ Γ) (finish : State → State)
    (adapt : ∀ state env, JoinContext names ghosts active frames state env → suffixPre (finish state) (select.pull env)) :
    ScalarJoins interp scalar (JoinContext names ghosts active frames)
      (fun state value => ∃ captured, suffixPre (finish state) captured ∧ value = Denote.term continuation captured)
      [] (.app (.var fn) (captureTuple Δ select)) := by
  apply ScalarJoins.jump
  intro state env h
  refine ⟨select.pull env, adapt state env h, ?_⟩
  change fn.get env (Denote.term (captureTuple Δ select) env) = _
  rw [h.known fn continuation.abstract known, denote_captureTuple]
  exact denote_abstract (Δ := []) continuation () (select.pull env)

end ScalarJoins
end Ariadne.Shallow.Adequacy

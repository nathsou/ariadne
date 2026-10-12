import Ariadne.Shallow.Adequacy.ReadExpr
import Ariadne.Shallow.Adequacy.Statements

namespace Ariadne.Shallow.Adequacy
open Core Heap

/-- Borrows are call-frame bindings. Observations have no write permission;
owners and borrows can also be immutable. No lifetime-bearing reference is
introduced by a local declaration or a container read. -/
inductive Access where
  | owner (writable : Bool)
  | borrow (writable : Bool)
  | observation
  deriving DecidableEq, Repr

def Access.writable : Access → Bool
  | .owner writable | .borrow writable => writable
  | .observation => false

def Access.ofBinding (binding : Check.Binding) : Access :=
  let writable := Check.referenceType binding.ty && !Check.immutable binding.ty &&
    !binding.readOnly && (match binding.ty with | .readonly _ => false | _ => true)
  if binding.borrowed then .borrow writable
  else if binding.readOnly then .observation else .owner writable

abbrev Accesses (Γ : List Core.Ty) := ∀ {t}, Var Γ t → Access
abbrev Footprints (Γ : List Core.Ty) := ∀ {t}, Var Γ t → Footprint

def Layouts.cons {interp : Named.Interp} (layout : DataRelation Value (t.denote interp))
    (layouts : Layouts Γ interp) : Layouts (t :: Γ) interp :=
  fun v => match v with | .here => layout | .there v => layouts v

def Accesses.cons (access : Access) (accesses : Accesses Γ) : Accesses (t :: Γ) :=
  fun v => match v with | .here => access | .there v => accesses v

def Footprints.cons (footprint : Footprint) (footprints : Footprints Γ) : Footprints (t :: Γ) :=
  fun v => match v with | .here => footprint | .there v => footprints v

/-- The stateful invariant relates every visible source cell to its current
native value. Writable footprints are separated from all other observations;
immutable observations may share. Binding cells are never owned data, so local
reassignment cannot invalidate a represented container. -/
structure OwnershipEnvironment {interp : Named.Interp} (names : Names Γ)
    (layouts : Layouts Γ interp) (accesses : Accesses Γ) (footprints : Footprints Γ)
    (state : State) (env : Core.Env Γ interp) : Prop where
  bindings : state.ValidBindings
  scalar : Environment names state env
  data : ∀ {t} (v : Var Γ t), names.visible v = true →
    ∃ value, state.lookup (names.get v) = .ok value ∧
      (layouts v).Holds state.heap value (v.get env) (footprints v)
  noCells : ∀ {t} (v : Var Γ t), names.visible v = true →
    ∀ {name address}, state.Binds name address → address ∉ footprints v
  separate : ∀ {a b} (v : Var Γ a) (w : Var Γ b),
    names.visible v = true → names.visible w = true → names.get v ≠ names.get w →
    ((accesses v).writable || (accesses w).writable) = true →
    Disjoint (footprints v) (footprints w)

theorem OwnershipEnvironment.read {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {footprints : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@footprints) state env) :
    ReadEnvironment names (@layouts) state env := by
  refine ⟨inputs.scalar, ?_⟩
  intro t v visible
  obtain ⟨value, lookup, related⟩ := inputs.data v visible
  exact ⟨value, footprints v, lookup, related⟩

/-- Heap mutation preserves each other represented value. Only the updated
owner's local representation must be proved by its primitive operation. -/
theorem OwnershipEnvironment.frame_other {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {footprints : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@footprints) state env)
    (target : Var Γ a) (visible : names.visible target = true)
    (writable : (accesses target).writable = true) (after : Heap)
    (writes : Modifies (footprints target) state.heap after)
    (other : Var Γ b) (observed : names.visible other = true)
    (distinct : names.get other ≠ names.get target) :
    ∃ value, state.lookup (names.get other) = .ok value ∧
      (layouts other).Holds after value (other.get env) (footprints other) := by
  obtain ⟨value, lookup, related⟩ := inputs.data other observed
  exact ⟨value, lookup, (layouts other).frame related
    (writes.frame ((layouts other).allocated related)
      (inputs.separate other target observed visible distinct (by simp [writable])))⟩

/-- A declaration introduces an owner or an immutable observation, never a
borrow. Separation and cell exclusion concern just the newly stored value;
old representations are framed across the allocation of its binding cell. -/
theorem OwnershipEnvironment.declare {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {footprints : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@footprints) state env)
    (name : String) (layout : DataRelation Value (t.denote interp))
    (value : Value) (native : t.denote interp) (footprint : Footprint) (writable : Bool)
    (related : layout.Holds state.heap value native footprint)
    (scalar : ∀ repr : Scalar t, value = repr.encode native)
    (noCells : ∀ {query address}, state.Binds query address → address ∉ footprint)
    (separate : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name →
      (writable || (accesses v).writable) = true → Disjoint footprint (footprints v)) :
    OwnershipEnvironment (names.cons name) (Layouts.cons layout (@layouts))
      (@Accesses.cons Γ t (.owner writable) (@accesses))
      (@Footprints.cons Γ t footprint (@footprints))
      (state.declare name value) (native, env) := by
  constructor
  · exact inputs.bindings.declare name value
  · intro u v repr visible
    cases v with
    | here => simpa only [Names.cons, Var.get, scalar repr] using lookup_declare_self state name value
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact lookup_declare_other seen.2.symm (inputs.scalar v repr seen.1)
  · intro u v visible
    cases v with
    | here =>
      exact ⟨value, lookup_declare_self state name value,
        layout.frame related (state.alloc_frame (.cell value) footprint (layout.allocated related))⟩
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      obtain ⟨old, lookup, represented⟩ := inputs.data v seen.1
      exact ⟨old, lookup_declare_other seen.2.symm lookup,
        (layouts v).frame represented (state.alloc_frame (.cell value) _ ((layouts v).allocated represented))⟩
  · intro u v visible query address bound
    rcases (state.binds_declare name query value address).mp bound with ⟨_, rfl⟩ | ⟨_, bound⟩
    · cases v with
      | here => exact state.alloc_fresh (.cell value) footprint (layout.allocated related)
      | there v =>
        have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
        obtain ⟨_, _, represented⟩ := inputs.data v seen.1
        exact state.alloc_fresh (.cell value) _ ((layouts v).allocated represented)
    · cases v with
      | here => exact noCells bound
      | there v =>
        have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
        exact inputs.noCells v seen.1 bound
  · intro a b v w hv hw distinct writing
    cases v with
    | here =>
      cases w with
      | here => exact False.elim (distinct rfl)
      | there w =>
        have seen : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact separate w seen.1 seen.2 writing
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using hv
      cases w with
      | here =>
        exact (separate v seen.1 seen.2 (by simpa [Accesses.cons, Access.writable, Bool.or_comm] using writing)).symm
      | there w =>
        have observed : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact inputs.separate v w seen.1 observed.1 distinct writing

/-- Local reassignment writes its binding cell, which is outside every data
footprint. The replaced Core version is hidden by `Names.cons`. -/
theorem OwnershipEnvironment.assign {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {footprints : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@footprints) state env)
    (name : String) (address : Nat) (bound : state.Binds name address)
    (layout : DataRelation Value (t.denote interp))
    (value : Value) (native : t.denote interp) (footprint : Footprint) (writable : Bool)
    (related : layout.Holds state.heap value native footprint)
    (scalar : ∀ repr : Scalar t, value = repr.encode native)
    (noCells : ∀ {query cell}, state.Binds query cell → cell ∉ footprint)
    (separate : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name →
      (writable || (accesses v).writable) = true → Disjoint footprint (footprints v)) :
    OwnershipEnvironment (names.cons name) (Layouts.cons layout (@layouts))
      (@Accesses.cons Γ t (.owner writable) (@accesses))
      (@Footprints.cons Γ t footprint (@footprints))
      {state with heap := state.heap.set address (.cell value)} (native, env) := by
  constructor
  · exact inputs.bindings.write address (.cell value)
  · intro u v repr visible
    cases v with
    | here => simpa only [Names.cons, Var.get, scalar repr] using
        State.lookup_written_self bound (inputs.bindings.allocated bound) value
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact State.lookup_written_other inputs.bindings bound seen.2.symm (inputs.scalar v repr seen.1) value
  · intro u v visible
    cases v with
    | here =>
      exact ⟨value, State.lookup_written_self bound (inputs.bindings.allocated bound) value,
        layout.frame related (agreesOn_set state.heap footprint address (.cell value) (noCells bound))⟩
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      obtain ⟨old, lookup, represented⟩ := inputs.data v seen.1
      exact ⟨old, State.lookup_written_other inputs.bindings bound seen.2.symm lookup value,
        (layouts v).frame represented (agreesOn_set state.heap _ address (.cell value)
          (inputs.noCells v seen.1 bound))⟩
  · intro u v visible query cell cellBound
    cases v with
    | here => exact noCells cellBound
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.noCells v seen.1 cellBound
  · intro a b v w hv hw distinct writing
    cases v with
    | here =>
      cases w with
      | here => exact False.elim (distinct rfl)
      | there w =>
        have seen : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact separate w seen.1 seen.2 writing
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using hv
      cases w with
      | here =>
        exact (separate v seen.1 seen.2 (by simpa [Accesses.cons, Access.writable, Bool.or_comm] using writing)).symm
      | there w =>
        have observed : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact inputs.separate v w seen.1 observed.1 distinct writing

/-- Discarding a local's native version discards its ownership obligation.
Source cells may remain allocated; they cannot become observable aliases. -/
theorem OwnershipEnvironment.drop {interp : Named.Interp} {names : Names (t :: Γ)}
    {layouts : Layouts (t :: Γ) interp} {accesses : Accesses (t :: Γ)}
    {footprints : Footprints (t :: Γ)} {state : State} {env : Core.Env (t :: Γ) interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@footprints) state env) :
    OwnershipEnvironment
      {get := fun v => names.get (.there v), visible := fun v => names.visible (.there v)}
      (fun v => layouts (.there v)) (fun v => accesses (.there v))
      (fun v => footprints (.there v)) state env.2 := by
  constructor
  · exact inputs.bindings
  · exact fun v repr seen => inputs.scalar (.there v) repr seen
  · exact fun v seen => inputs.data (.there v) seen
  · intro u v seen query address bound
    exact inputs.noCells (.there v) seen bound
  · exact fun v w hv hw different writing => inputs.separate (.there v) (.there w) hv hw different writing

end Ariadne.Shallow.Adequacy

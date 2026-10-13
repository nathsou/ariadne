import Ariadne.Shallow.Adequacy.Ownership

namespace Ariadne.Shallow.Adequacy
open Core Heap

/-- Read footprints may include shared immutable descendants. Separate write
footprints permit that sharing without requiring disjoint read footprints. -/
structure PermissionEnvironment {interp : Named.Interp} (names : Names Γ)
    (layouts : Layouts Γ interp) (accesses : Accesses Γ)
    (reads writes : Footprints Γ) (state : State) (env : Core.Env Γ interp) : Prop where
  bindings : state.ValidBindings
  scalar : Environment names state env
  data : ∀ {t} (v : Var Γ t), names.visible v = true →
    ∃ value, state.lookup (names.get v) = .ok value ∧
      (layouts v).Holds state.heap value (v.get env) (reads v)
  permitted : ∀ {t} (v : Var Γ t), names.visible v = true → writes v ⊆ reads v
  readonly : ∀ {t} (v : Var Γ t), names.visible v = true →
    (accesses v).writable = false → writes v = []
  noCells : ∀ {t} (v : Var Γ t), names.visible v = true →
    ∀ {name address}, state.Binds name address → address ∉ reads v
  separate : ∀ {a b} (v : Var Γ a) (w : Var Γ b),
    names.visible v = true → names.visible w = true → names.get v ≠ names.get w →
    Disjoint (reads v) (writes w)

def coarseWrites (accesses : Accesses Γ) (reads : Footprints Γ) : Footprints Γ :=
  fun v => if (accesses v).writable then reads v else []

/-- Every existing ownership witness remains a valid permission witness. The
refinement additionally admits shared reads when their write domains separate. -/
theorem OwnershipEnvironment.permissions {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : OwnershipEnvironment names (@layouts) (@accesses) (@reads) state env) :
    PermissionEnvironment names (@layouts) (@accesses) (@reads)
      (@coarseWrites Γ (@accesses) (@reads)) state env := by
  refine ⟨inputs.bindings, inputs.scalar, inputs.data, ?_, ?_, inputs.noCells, ?_⟩
  · intro t v _
    simp only [coarseWrites]
    split <;> simp
  · intro t v _ readonly
    simp [coarseWrites, readonly]
  · intro a b v w hv hw distinct
    by_cases writable : (accesses w).writable = true
    · simpa [coarseWrites, writable] using
        inputs.separate v w hv hw distinct (by simp [writable])
    · simp [coarseWrites, writable, Disjoint]

theorem PermissionEnvironment.read {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads writes : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env) :
    ReadEnvironment names (@layouts) state env := by
  refine ⟨inputs.scalar, ?_⟩
  intro t v visible
  obtain ⟨value, lookup, related⟩ := inputs.data v visible
  exact ⟨value, reads v, lookup, related⟩

/-- Local storage introduces an owner, never a borrow. Read sharing and write
separation are checked independently, and the fresh binding cell is framed. -/
theorem PermissionEnvironment.declare {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads writes : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env)
    (name : String) (layout : DataRelation Value (t.denote interp))
    (value : Value) (native : t.denote interp) (read write : Footprint) (writable : Bool)
    (related : layout.Holds state.heap value native read)
    (scalar : ∀ repr : Scalar t, value = repr.encode native)
    (permitted : write ⊆ read) (readonly : writable = false → write = [])
    (noCells : ∀ {query address}, state.Binds query address → address ∉ read)
    (newRead : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name →
      Disjoint read (writes v))
    (newWrite : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name →
      Disjoint (reads v) write) :
    PermissionEnvironment (names.cons name) (Layouts.cons layout (@layouts))
      (@Accesses.cons Γ t (.owner writable) (@accesses))
      (@Footprints.cons Γ t read (@reads)) (@Footprints.cons Γ t write (@writes))
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
    | here => exact ⟨value, lookup_declare_self state name value,
        layout.frame related (state.alloc_frame (.cell value) read (layout.allocated related))⟩
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      obtain ⟨old, lookup, represented⟩ := inputs.data v seen.1
      exact ⟨old, lookup_declare_other seen.2.symm lookup,
        (layouts v).frame represented (state.alloc_frame (.cell value) _ ((layouts v).allocated represented))⟩
  · intro u v visible
    cases v with
    | here => exact permitted
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.permitted v seen.1
  · intro u v visible immutable
    cases v with
    | here => exact readonly immutable
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.readonly v seen.1 immutable
  · intro u v visible query address bound
    rcases (state.binds_declare name query value address).mp bound with ⟨_, rfl⟩ | ⟨_, bound⟩
    · cases v with
      | here => exact state.alloc_fresh (.cell value) read (layout.allocated related)
      | there v =>
        have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
        obtain ⟨_, _, represented⟩ := inputs.data v seen.1
        exact state.alloc_fresh (.cell value) _ ((layouts v).allocated represented)
    · cases v with
      | here => exact noCells bound
      | there v =>
        have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
        exact inputs.noCells v seen.1 bound
  · intro a b v w hv hw distinct
    cases v with
    | here =>
      cases w with
      | here => exact False.elim (distinct rfl)
      | there w =>
        have seen : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact newRead w seen.1 seen.2
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using hv
      cases w with
      | here => exact newWrite v seen.1 seen.2
      | there w =>
        have observed : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact inputs.separate v w seen.1 observed.1 distinct

/-- A temporary projection can write only within its owner's permission.
Every other visible value is framed, even when read footprints overlap. -/
theorem PermissionEnvironment.frame_projection {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads writes : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env)
    (target : Var Γ a) (visible : names.visible target = true)
    (selected : Footprint) (within : selected ⊆ writes target) (after : Heap)
    (modified : Modifies selected state.heap after)
    (other : Var Γ b) (observed : names.visible other = true)
    (distinct : names.get other ≠ names.get target) :
    ∃ value, state.lookup (names.get other) = .ok value ∧
      (layouts other).Holds after value (other.get env) (reads other) := by
  obtain ⟨value, lookup, related⟩ := inputs.data other observed
  refine ⟨value, lookup, (layouts other).frame related (modified.frame ((layouts other).allocated related) ?_)⟩
  intro address read selected
  exact inputs.separate other target observed visible distinct address read (within selected)

/-- Finish a statement-local mutation by restoring the complete environment.
The source binding still points to the same object; only its native version
changes. Shadowing hides the old version and preserves the original access,
including a parameter borrow, without allocating or assigning a binding cell.
The selected write domain may be smaller than the owner's read footprint. -/
theorem PermissionEnvironment.mutate {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads writes : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env)
    (target : Var Γ t) (visible : names.visible target = true)
    (selected : Footprint) (within : selected ⊆ writes target) (after : Heap)
    (modified : Modifies selected state.heap after)
    (value : Value) (lookup : state.lookup (names.get target) = .ok value)
    (native : t.denote interp)
    (related : (layouts target).Holds after value native (reads target))
    (scalar : ∀ repr : Scalar t, value = repr.encode native) :
    PermissionEnvironment (names.cons (names.get target))
      (Layouts.cons (layouts target) (@layouts))
      (@Accesses.cons Γ t (accesses target) (@accesses))
      (@Footprints.cons Γ t (reads target) (@reads))
      (@Footprints.cons Γ t (writes target) (@writes))
      {state with heap := after} (native, env) := by
  have cells : ∀ {query address}, state.Binds query address →
      state.heap[address]? = after[address]? := by
    intro query address bound
    apply modified.2 address (inputs.bindings.allocated bound)
    intro member
    exact inputs.noCells target visible bound (inputs.permitted target visible (within member))
  constructor
  · exact inputs.bindings.heap after modified.1
  · intro u v repr seen
    cases v with
    | here => simpa only [Names.cons, Var.get, scalar repr] using State.lookup_heap lookup after cells
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using seen
      exact State.lookup_heap (inputs.scalar v repr observed.1) after cells
  · intro u v seen
    cases v with
    | here => exact ⟨value, State.lookup_heap lookup after cells, related⟩
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using seen
      obtain ⟨old, lookup, represented⟩ :=
        inputs.frame_projection target visible selected within after modified v observed.1 observed.2
      exact ⟨old, State.lookup_heap lookup after cells, represented⟩
  · intro u v seen
    cases v with
    | here => exact inputs.permitted target visible
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using seen
      exact inputs.permitted v observed.1
  · intro u v seen immutable
    cases v with
    | here => exact inputs.readonly target visible immutable
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using seen
      exact inputs.readonly v observed.1 immutable
  · intro u v seen query address bound
    cases v with
    | here => exact inputs.noCells target visible bound
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using seen
      exact inputs.noCells v observed.1 bound
  · intro a b v w hv hw distinct
    cases v with
    | here =>
      cases w with
      | here => exact False.elim (distinct rfl)
      | there w =>
        have observed : names.visible w = true ∧ names.get w ≠ names.get target := by
          simpa [Names.cons] using hw
        exact inputs.separate target w visible observed.1 distinct
    | there v =>
      have observed : names.visible v = true ∧ names.get v ≠ names.get target := by
        simpa [Names.cons] using hv
      cases w with
      | here => exact inputs.separate v target observed.1 visible observed.2
      | there w =>
        have other : names.visible w = true ∧ names.get w ≠ names.get target := by
          simpa [Names.cons] using hw
        exact inputs.separate v w observed.1 other.1 distinct

/-- Reassignment changes a binding cell, outside every data read footprint.
The previous native version is hidden, so its permission is not duplicated. -/
theorem PermissionEnvironment.assign {interp : Named.Interp} {names : Names Γ}
    {layouts : Layouts Γ interp} {accesses : Accesses Γ} {reads writes : Footprints Γ}
    {state : State} {env : Core.Env Γ interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env)
    (name : String) (address : Nat) (bound : state.Binds name address)
    (layout : DataRelation Value (t.denote interp))
    (value : Value) (native : t.denote interp) (read write : Footprint) (writable : Bool)
    (related : layout.Holds state.heap value native read)
    (scalar : ∀ repr : Scalar t, value = repr.encode native)
    (permitted : write ⊆ read) (readonly : writable = false → write = [])
    (noCells : ∀ {query cell}, state.Binds query cell → cell ∉ read)
    (newRead : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name → Disjoint read (writes v))
    (newWrite : ∀ {u} (v : Var Γ u), names.visible v = true → names.get v ≠ name → Disjoint (reads v) write) :
    PermissionEnvironment (names.cons name) (Layouts.cons layout (@layouts))
      (@Accesses.cons Γ t (.owner writable) (@accesses))
      (@Footprints.cons Γ t read (@reads)) (@Footprints.cons Γ t write (@writes))
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
    | here => exact ⟨value, State.lookup_written_self bound (inputs.bindings.allocated bound) value,
        layout.frame related (agreesOn_set state.heap read address (.cell value) (noCells bound))⟩
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      obtain ⟨old, lookup, represented⟩ := inputs.data v seen.1
      exact ⟨old, State.lookup_written_other inputs.bindings bound seen.2.symm lookup value,
        (layouts v).frame represented (agreesOn_set state.heap _ address (.cell value) (inputs.noCells v seen.1 bound))⟩
  · intro u v visible
    cases v with
    | here => exact permitted
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.permitted v seen.1
  · intro u v visible immutable
    cases v with
    | here => exact readonly immutable
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.readonly v seen.1 immutable
  · intro u v visible query cell cellBound
    cases v with
    | here => exact noCells cellBound
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using visible
      exact inputs.noCells v seen.1 cellBound
  · intro a b v w hv hw distinct
    cases v with
    | here =>
      cases w with
      | here => exact False.elim (distinct rfl)
      | there w =>
        have seen : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact newRead w seen.1 seen.2
    | there v =>
      have seen : names.visible v = true ∧ names.get v ≠ name := by simpa [Names.cons] using hv
      cases w with
      | here => exact newWrite v seen.1 seen.2
      | there w =>
        have observed : names.visible w = true ∧ names.get w ≠ name := by simpa [Names.cons] using hw
        exact inputs.separate v w seen.1 observed.1 distinct

theorem PermissionEnvironment.drop {interp : Named.Interp} {names : Names (t :: Γ)}
    {layouts : Layouts (t :: Γ) interp} {accesses : Accesses (t :: Γ)}
    {reads writes : Footprints (t :: Γ)} {state : State} {env : Core.Env (t :: Γ) interp}
    (inputs : PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state env) :
    PermissionEnvironment
      {get := fun v => names.get (.there v), visible := fun v => names.visible (.there v)}
      (fun v => layouts (.there v)) (fun v => accesses (.there v))
      (fun v => reads (.there v)) (fun v => writes (.there v)) state env.2 := by
  constructor
  · exact inputs.bindings
  · exact fun v repr seen => inputs.scalar (.there v) repr seen
  · exact fun v seen => inputs.data (.there v) seen
  · exact fun v seen => inputs.permitted (.there v) seen
  · exact fun v seen => inputs.readonly (.there v) seen
  · intro u v seen name address bound
    exact inputs.noCells (.there v) seen bound
  · exact fun v w hv hw distinct => inputs.separate (.there v) (.there w) hv hw distinct

end Ariadne.Shallow.Adequacy

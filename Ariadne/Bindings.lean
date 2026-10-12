import Ariadne.Value

namespace Ariadne

/-- The visible lexical binding, separated from its stored value. -/
def State.Binds (state : State) (name : String) (address : Nat) : Prop :=
  state.env.find? (fun entry => entry.1 == name) = some (name, address)

/-- Binding cells are allocated, and distinct visible names do not share a cell.
Reference values stored inside cells may still be shared read-only. -/
structure State.ValidBindings (state : State) : Prop where
  allocated : ∀ {name address}, state.Binds name address → address < state.heap.length
  separate : ∀ {left right address}, state.Binds left address → state.Binds right address → left = right

theorem State.binds_empty (state : State) : ({state with env := []} : State).ValidBindings := by
  constructor
  · intro name address h; cases h
  · intro left right address h; cases h

theorem State.binds_declare (state : State) (name query : String) (value : Value) (address : Nat) :
    (state.declare name value).Binds query address ↔
      (query = name ∧ address = state.heap.length) ∨ (query ≠ name ∧ state.Binds query address) := by
  by_cases same : name = query
  · subst query
    simp [State.Binds, State.declare, State.alloc]
    omega
  · simp [State.Binds, State.declare, State.alloc, same, Ne.symm same]

theorem State.ValidBindings.declare {state : State} (valid : state.ValidBindings) (name : String) (value : Value) :
    (state.declare name value).ValidBindings := by
  constructor
  · intro query address bound
    rcases (state.binds_declare name query value address).mp bound with ⟨_, rfl⟩ | ⟨_, bound⟩
    · simp [State.declare, State.alloc]
    · have := valid.allocated bound
      simp [State.declare, State.alloc]; omega
  · intro left right address hl hr
    rcases (state.binds_declare name left value address).mp hl with hl | hl
    · rcases (state.binds_declare name right value address).mp hr with hr | hr
      · exact hl.1.trans hr.1.symm
      · have := valid.allocated hr.2; omega
    · rcases (state.binds_declare name right value address).mp hr with hr | hr
      · have := valid.allocated hl.2; omega
      · exact valid.separate hl.2 hr.2

theorem State.lookup_binds {state : State} {name : String} {value : Value}
    (lookup : state.lookup name = .ok value) :
    ∃ address, state.Binds name address ∧ state.heap[address]? = some (.cell value) := by
  cases found : state.env.find? (fun entry => entry.1 == name) with
  | none => simp [State.lookup, found] at lookup
  | some entry =>
    have named : entry.1 = name := by
      simpa using List.find?_some (p := fun entry : String × Nat => entry.1 == name) found
    rcases entry with ⟨_, address⟩
    dsimp only at named
    subst name
    refine ⟨address, found, ?_⟩
    cases stored : state.heap[address]? with
    | none => simp [State.lookup, found, stored] at lookup
    | some object =>
      cases object <;> simp [State.lookup, found, stored, pure, Except.pure] at lookup
      case cell existing => subst value; rfl

theorem State.assign_bound {state : State} {name : String} {address : Nat}
    (bound : state.Binds name address) (allocated : address < state.heap.length) (value : Value) :
    state.assign name value = .ok {state with heap := state.heap.set address (.cell value)} := by
  simp [State.assign, State.Binds] at bound ⊢
  simp [bound, State.write, allocated]

theorem State.lookup_written_self {state : State} {name : String} {address : Nat}
    (bound : state.Binds name address) (allocated : address < state.heap.length) (value : Value) :
    ({state with heap := state.heap.set address (.cell value)} : State).lookup name = .ok value := by
  change state.env.find? (fun entry => entry.1 == name) = some (name, address) at bound
  simp [State.lookup, bound, allocated, pure, Except.pure]

theorem State.lookup_written_other {state : State} {name query : String} {address : Nat}
    (valid : state.ValidBindings) (bound : state.Binds name address) (distinct : name ≠ query)
    {existing : Value} (lookup : state.lookup query = .ok existing) (value : Value) :
    ({state with heap := state.heap.set address (.cell value)} : State).lookup query = .ok existing := by
  obtain ⟨other, queried, stored⟩ := lookup_binds lookup
  have different : other ≠ address := by intro same; subst other; exact distinct (valid.separate bound queried)
  change state.env.find? (fun entry => entry.1 == query) = some (query, other) at queried
  simp [State.lookup, queried, List.getElem?_set_ne (Ne.symm different), stored, pure, Except.pure]

theorem State.ValidBindings.write {state : State} (valid : state.ValidBindings) (address : Nat) (object : Object) :
    ({state with heap := state.heap.set address object} : State).ValidBindings := by
  constructor
  · intro name loc bound; simpa using valid.allocated bound
  · exact valid.separate

end Ariadne

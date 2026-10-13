import Ariadne.Shallow.Adequacy.Permissions

namespace Ariadne.Shallow.Adequacy
open Heap

/-- Parameter binding allocates cells without changing any preexisting data. -/
theorem bindArguments_modifies (state : State) (params : List Param) (args : List Value) (owned : Footprint) :
    Modifies owned state.heap (bindArguments state params args).heap := by
  have bind : ∀ (entries : List (Param × Value)) (state : State),
      Modifies owned state.heap (entries.foldl (fun state (param, value) => state.declare param.name value) state).heap := by
    intro entries
    induction entries with
    | nil => intro state; exact Modifies.refl ..
    | cons entry entries ih =>
      intro state
      exact (modifies_append state.heap [.cell entry.2] owned).trans (ih (state.declare entry.1.name entry.2))
  exact bind (params.zip args) {state with env := []}

/-- Every visible call-frame cell lies beyond the original input heap. This
holds even for shadowed names, without a uniqueness or separation premise. -/
theorem bindArguments_cell_fresh (state : State) (params : List Param) (args : List Value)
    {name : String} {address : Nat} (bound : (bindArguments state params args).Binds name address) :
    state.heap.length ≤ address := by
  have bind : ∀ (entries : List (Param × Value)) (before : State),
      state.heap.length ≤ before.heap.length →
      (∀ {name address}, before.Binds name address → state.heap.length ≤ address) →
      ∀ {name address}, (entries.foldl (fun state (param, value) => state.declare param.name value) before).Binds name address →
        state.heap.length ≤ address := by
    intro entries
    induction entries with
    | nil => intro before grows fresh name address bound; exact fresh bound
    | cons entry entries ih =>
      intro before grows fresh name address bound
      apply ih (before.declare entry.1.name entry.2) (by simpa [State.declare, State.alloc] using Nat.le_trans grows (Nat.le_succ before.heap.length)) _ bound
      intro query cell declared
      rcases (before.binds_declare entry.1.name query entry.2 cell).mp declared with ⟨_, rfl⟩ | ⟨_, old⟩
      · exact grows
      · exact fresh old
  exact bind (params.zip args) {state with env := []} (Nat.le_refl _) (by intro query cell bound; cases bound) bound

/-- Represented input footprints cannot contain newly allocated parameter cells. -/
theorem bindArguments_noCells {layout : DataRelation Value α} {state : State}
    {value : Value} {native : α} {owned : Footprint}
    (input : layout.Holds state.heap value native owned) (params : List Param) (args : List Value)
    {name : String} {address : Nat} (bound : (bindArguments state params args).Binds name address) :
    address ∉ owned := by
  intro member
  have allocated := layout.allocated input address member
  have fresh := bindArguments_cell_fresh state params args bound
  omega

/-- Mutation within an input footprint preserves every parameter lookup,
without separately assuming that its binding cells are outside that footprint. -/
theorem bindArguments_lookup_frame {layout : DataRelation Value α} {state : State}
    {value : Value} {native : α} {owned selected : Footprint}
    (input : layout.Holds state.heap value native owned) (params : List Param) (args : List Value)
    (after : Heap) (within : selected ⊆ owned)
    (modified : Modifies selected (bindArguments state params args).heap after)
    {name : String} {observed : Value}
    (lookup : (bindArguments state params args).lookup name = .ok observed) :
    ({bindArguments state params args with heap := after} : State).lookup name = .ok observed := by
  apply State.lookup_heap lookup after
  intro query address bound
  apply modified.2 address ((bindArguments_valid state params args).allocated bound)
  intro member
  exact bindArguments_noCells input params args bound (within member)

end Ariadne.Shallow.Adequacy

import Ariadne.Shallow.Prelude.Map
import Ariadne.Shallow.Prelude.Array

namespace Ariadne.Shallow

/-- A projection may fail, as array indexing and Map lookup do. Updates are
specified only where the getter succeeds, matching the generated safety guard. -/
structure Lens (container focus : Type) where
  get : container → Option focus
  put : container → focus → container
  get_put : ∀ {state old}, get state = some old → ∀ value, get (put state value) = some value
  put_get : ∀ {state value}, get state = some value → put state value = state
  put_put : ∀ {state old}, get state = some old → ∀ first second,
    put (put state first) second = put state second

def Lens.modify (lens : Lens container focus) (update : focus → focus) (state : container) : container :=
  match lens.get state with
  | none => state
  | some value => lens.put state (update value)

def Lens.safe (lens : Lens container focus) (state : container) : Bool := (lens.get state).isSome

theorem Lens.modify_get (lens : Lens container focus) (update : focus → focus)
    {state : container} {value : focus} (found : lens.get state = some value) :
    lens.get (lens.modify update state) = some (update value) := by
  simp only [Lens.modify, found]
  exact lens.get_put found _

theorem Lens.modify_identity (lens : Lens container focus) (state : container) :
    lens.modify id state = state := by
  cases found : lens.get state with
  | none => simp [Lens.modify, found]
  | some value => simpa only [Lens.modify, found, id] using lens.put_get found

theorem Lens.modify_compose (lens : Lens container focus) (first second : focus → focus) (state : container) :
    lens.modify second (lens.modify first state) = lens.modify (second ∘ first) state := by
  cases found : lens.get state with
  | none => simp [Lens.modify, found]
  | some value =>
    simp only [Lens.modify, found, lens.get_put found, Function.comp_apply]
    exact lens.put_put found _ _

private theorem entries_put_get [BEq key] (entries : List (key × value))
    (query : key) (value : value) (found : MapEntries.get entries query = some value) :
    MapEntries.set entries query value = entries := by
  induction entries with
  | nil => simp [MapEntries.get] at found
  | cons head rest ih =>
    rcases head with ⟨key, old⟩
    by_cases same : (key == query) = true
    · have equal : value = old := by simpa [MapEntries.get, same] using found.symm
      simp [MapEntries.set, same, equal]
    · simp only [MapEntries.get, same, Bool.false_eq_true, ↓reduceIte] at found
      simp only [MapEntries.set, same, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (List.cons (key, old)) (ih found)

private theorem entries_put_put [BEq key] [EquivBEq key] (entries : List (key × value))
    (query : key) (first second : value) :
    MapEntries.set (MapEntries.set entries query first) query second = MapEntries.set entries query second := by
  induction entries with
  | nil => simp [MapEntries.set]
  | cons head rest ih =>
    rcases head with ⟨key, old⟩
    by_cases same : (key == query) = true <;> simp [MapEntries.set, same, ih]

def Lens.map [BEq key] [EquivBEq key] (query : key) : Lens (JSMap key value) value where
  get state := state.get query
  put state value := state.set query value
  get_put := by intro state old _ value; simp [JSMap.get_set]
  put_get := by
    intro state value found
    apply JSMap.ext
    change MapEntries.set state.entries query value = state.entries
    exact entries_put_get state.entries query value found
  put_put := by
    intro state old _ first second
    exact JSMap.ext (entries_put_put state.entries query first second)

private theorem list_put_get (state : List value) (index : Nat) (value : value)
    (found : state[index]? = some value) : state.set index value = state := by
  induction state generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index =>
      have tail : rest[index]? = some value := by simpa using found
      simpa using congrArg (List.cons head) (ih index tail)

def Lens.array (index : Nat) : Lens (List value) value where
  get state := state[index]?
  put state value := state.set index value
  get_put := by
    intro state old found value
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).choose
  put_get := fun found => list_put_get _ _ _ found
  put_put := by intro state old _ first second; exact List.set_set first

def Lens.compose (outer : Lens container middle) (inner : Lens middle focus) : Lens container focus where
  get state := (outer.get state).bind inner.get
  put state value := match outer.get state with
    | none => state
    | some middle => outer.put state (inner.put middle value)
  get_put := by
    intro state old found value
    cases selected : outer.get state with
    | none => simp [selected] at found
    | some middle =>
      have focused : inner.get middle = some old := by simpa [selected] using found
      simp only [outer.get_put selected, Option.bind_some]
      exact inner.get_put focused value
  put_get := by
    intro state value found
    cases selected : outer.get state with
    | none => simp [selected] at found
    | some middle =>
      have focused : inner.get middle = some value := by simpa [selected] using found
      simpa only [selected, inner.put_get focused] using outer.put_get selected
  put_put := by
    intro state old found first second
    cases selected : outer.get state with
    | none => simp [selected] at found
    | some middle =>
      have focused : inner.get middle = some old := by simpa [selected] using found
      simp only [outer.get_put selected, inner.put_put focused, outer.put_put selected]

end Ariadne.Shallow

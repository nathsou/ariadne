import Ariadne.Certificate

namespace Ariadne

/-- A postcondition on both the returned value and the final heap. -/
def Ensures (program : Program) (name : String) (args : List Value)
    (post : Value → State → Prop) : Prop :=
  ∀ fuel value state, runState program name fuel args = .ok (value, state) → post value state

/-- A concrete, terminating execution with a heap-aware postcondition. -/
def Reaches (program : Program) (name : String) (args : List Value)
    (post : Value → State → Prop) : Prop :=
  ∃ fuel value state, runState program name fuel args = .ok (value, state) ∧ post value state

def SourceReaches (source name : String) (args : List Value)
    (post : Value → State → Prop) : Prop :=
  ∃ program, frontend source = .ok program ∧ Reaches program name args post

theorem Certificate.transfer_reaches {source : String} (c : Certificate source)
    {name : String} {args : List Value} {post : Value → State → Prop}
    (h : Reaches c.program name args post) : SourceReaches source name args post :=
  ⟨c.program, c.checked, h⟩

/-- Extract a dense array observation without exposing allocation addresses in proofs. -/
def arrayResult (result : Result (Value × State)) : Result (List Value) := do
  let (value, state) ← result
  let .ref location := value | throw (.typeError "expected an array result")
  let some (.array values) := state.heap[location]?
    | throw (.typeError "expected an array result")
  return values

def mapResult (result : Result (Value × State)) : Result (List (Value × Value)) := do
  let (value, state) ← result
  let .ref location := value | throw (.typeError "expected a Map result")
  let some (.map values) := state.heap[location]?
    | throw (.typeError "expected a Map result")
  return values

/-- A successful partial observation cannot hide a failed program execution. -/
theorem array_reaches {program : Program} {name : String} {args : List Value}
    {fuel : Nat} {values : List Value}
    (observed : arrayResult (runState program name fuel args) = .ok values) :
    Reaches program name args (fun value state => arrayResult (.ok (value, state)) = .ok values) := by
  cases hr : runState program name fuel args with
  | error err => rw [hr] at observed; cases observed
  | ok pair =>
    rcases pair with ⟨value, state⟩
    rw [hr] at observed
    exact ⟨fuel, value, state, hr, observed⟩

theorem map_reaches {program : Program} {name : String} {args : List Value}
    {fuel : Nat} {values : List (Value × Value)}
    (observed : mapResult (runState program name fuel args) = .ok values) :
    Reaches program name args (fun value state => mapResult (.ok (value, state)) = .ok values) := by
  cases hr : runState program name fuel args with
  | error err => rw [hr] at observed; cases observed
  | ok pair =>
    rcases pair with ⟨value, state⟩
    rw [hr] at observed
    exact ⟨fuel, value, state, hr, observed⟩

/-- Local mutation writes the newly allocated cell and leaves older heap cells intact. -/
theorem declare_lookup (state : State) (name : String) (value : Value) :
    (state.declare name value).lookup name = .ok value := by
  simp [State.declare, State.alloc, State.lookup]
  rfl

/-- Replacing an entry never changes the list length when the key already exists. -/
theorem mapSet_length_of_has (entries : List (Value × Value)) (key value : Value)
    (h : mapHas entries key = true) : (mapSet entries key value).length = entries.length := by
  induction entries with
  | nil => simp [mapHas] at h
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    unfold mapSet
    split
    · rfl
    · rename_i hk
      simp only [mapHas, List.any_cons, Bool.or_eq_true] at h
      have hr : mapHas rest key = true := by
        rcases h with h | h
        · exact False.elim (hk h)
        · exact h
      simp [ih hr]

/-- Lookup after insertion needs only reflexivity for the canonicalized key.
This is the precise obligation imposed on a modeled key equality. -/
theorem mapGet_set (entries : List (Value × Value)) (key value : Value)
    (hkey : sameValueZero (canonicalKey key) key = true) :
    mapGet (mapSet entries key value) key = value := by
  induction entries with
  | nil => simp [mapSet, mapGet, hkey]
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : sameValueZero k key = true
    · simp [mapSet, mapGet, h]
    · simpa [mapSet, mapGet, h] using ih

@[simp] theorem bigint_key_reflexive (key : Int) :
    sameValueZero (canonicalKey (.bigint key)) (.bigint key) = true := by
  simp [sameValueZero, canonicalKey, strictEqual]

@[simp] theorem string_key_reflexive (key : JSString) :
    sameValueZero (canonicalKey (.string key)) (.string key) = true := by
  simp [sameValueZero, canonicalKey, strictEqual]

/-- An update to an existing Map key preserves both size and its new value. -/
theorem bigint_map_update (entries : List (Value × Value)) (key : Int) (value : Value)
    (existsKey : mapHas entries (.bigint key) = true) :
    (mapSet entries (.bigint key) value).length = entries.length ∧
    mapGet (mapSet entries (.bigint key) value) (.bigint key) = value :=
  ⟨mapSet_length_of_has entries _ value existsKey,
    mapGet_set entries _ value (bigint_key_reflexive key)⟩

end Ariadne

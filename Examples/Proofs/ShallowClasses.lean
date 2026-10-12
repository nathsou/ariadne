import Examples.Shallow.classes
namespace Examples.Proofs.ShallowClasses
open Ariadne.Shallow Extracted_classes.Shallow
abbrev Counter := NativeTypes.«Counter#state»
abbrev Seeded := NativeTypes.«Seeded#state»
theorem fresh_value : («Counter##new»).value = 0 := rfl
theorem fresh_counts (key : Ariadne.JSString) : («Counter##new»).counts.get key = none := by simp [«Counter##new»]
theorem seeded_value (initial : Int) : («Seeded##new» initial).value = initial := rfl
theorem add_value (state : Counter) (amount : Int) :
    («Counter#add» state amount).2.1.value = state.value + amount := rfl
theorem add_counts (state : Counter) (amount : Int) :
    («Counter#add» state amount).2.1.counts = state.counts := rfl
theorem twice_value (state : Counter) (amount : Int) :
    («Counter#twice» state amount).1 = state.value + 2 * amount := by
  simp [«Counter#twice»]; omega
theorem twice_state (state : Counter) (amount : Int) :
    («Counter#twice» state amount).2.1.value = state.value + 2 * amount := by
  simp [«Counter#twice»]; omega
theorem bump_value_preserved (state : Counter) (key : Ariadne.JSString) :
    («Counter#bump» state key).2.1.value = state.value := by
  cases found : state.counts.get key <;> simp [«Counter#bump», found]
theorem bump_lookup (state : Counter) (key : Ariadne.JSString) :
    («Counter#bump» state key).2.1.counts.get key = some ((state.counts.get key).getD 0 + 1) := by
  cases found : state.counts.get key <;> simp [«Counter#bump», found]
theorem bump_other (state : Counter) (key other : Ariadne.JSString) (different : key ≠ other) :
    («Counter#bump» state key).2.1.counts.get other = state.counts.get other := by
  cases found : state.counts.get key <;> simp [«Counter#bump», found, JSMap.get_set, different]
theorem use_counter (key : Ariadne.JSString) : useCounter key = 8 := by simp [useCounter]
theorem use_seeded (value : Int) : useSeeded value = value + 2 := rfl
theorem borrowed_bump (state : Counter) (key : Ariadne.JSString) :
    (bumpBorrowed state key).2.1.counts.get key = some ((state.counts.get key).getD 0 + 1) := by
  cases found : state.counts.get key <;> simp [bumpBorrowed, found]
theorem borrowed_add (state : Seeded) (amount : Int) :
    (addBorrowed state amount).2.1.value = state.value + amount := rfl
end Examples.Proofs.ShallowClasses

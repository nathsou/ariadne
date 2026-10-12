import Examples.Shallow.state

namespace Examples.Proofs.ShallowState
open Ariadne.Shallow Extracted_state.Shallow
abbrev Store := JSMap Ariadne.JSString Int

theorem bump_equation (store : Store) (key : Ariadne.JSString) :
    bump store key = ((store.get key).getD 0 + 1, store.set key ((store.get key).getD 0 + 1), ()) := by
  cases found : store.get key <;> simp [bump, found]

theorem bump_lookup (store : Store) (key : Ariadne.JSString) :
    (bump store key).2.1.get key = some ((store.get key).getD 0 + 1) := by
  rw [bump_equation]
  exact JSMap.get_set_self _ _ _

theorem bump_preserves_other (store : Store) (key other : Ariadne.JSString) (distinct : key ≠ other) :
    (bump store key).2.1.get other = store.get other := by
  simp [bump_equation, JSMap.get_set, distinct]

theorem twice_result (store : Store) (key : Ariadne.JSString) :
    (twice store key).1 = 2 * (store.get key).getD 0 + 3 := by
  cases found : store.get key <;> simp [twice, found] <;> omega

theorem twice_lookup (store : Store) (key : Ariadne.JSString) :
    (twice store key).2.1.get key = some ((store.get key).getD 0 + 2) := by
  cases found : store.get key <;> simp [twice, found, Int.add_assoc]

theorem transfer_missing (source target : Store) (key : Ariadne.JSString) (missing : source.get key = none) :
    transfer source target key = ((), source, target, ()) := by simp [transfer, missing]

theorem transfer_present (source target : Store) (key : Ariadne.JSString) (value : Int)
    (found : source.get key = some value) :
    transfer source target key = ((), source.delete key, target.set key value, ()) := by
  simp [transfer, found]

theorem early_skipped (store : Store) : early store true = ((), store, ()) := rfl

theorem fresh_call (key : Ariadne.JSString) : fromFresh key = 1 := by simp [fromFresh]

theorem pureCopy_equation (values : List Int) : pureCopy values = values := rfl

theorem copyCaller_equation (values : List Int) : copyCaller values = values ++ [9] := rfl

private theorem append_loop (xs captured initial : List Int) :
    Exit.elim (Loop.each xs (initial, initial, captured, ()) JoinNative.«append#0»)
      JoinNative.«append#1» id = ((), initial ++ xs, ()) := by
  induction xs generalizing initial with
  | nil => simp [Loop.each, Exit.elim]
  | cons x xs ih =>
    simpa only [Loop.each, JoinNative.«append#0», List.append_assoc, List.cons_append, List.nil_append]
      using ih (initial ++ [x])

theorem append_equation (values items : List Int) : append values items = ((), values ++ items, ()) :=
  append_loop items items values

end Examples.Proofs.ShallowState

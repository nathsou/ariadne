import Ariadne.Shallow.Lemmas.Prelude
import Ariadne.Shallow.Prelude.NumericCollections
namespace Ariadne.Shallow

/-- Deletion removes at most one key equivalence class. The unique-key
invariant is necessary: filtering an arbitrary entry list could remove more. -/
private theorem filter_length [BEq κ] [EquivBEq κ] (keys : List κ) (query : κ)
    (unique : keys.Pairwise (fun a b => (a == b) = false)) :
    (keys.filter (fun key => !(key == query))).length + (keys.any (· == query)).toNat = keys.length := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    rcases List.pairwise_cons.mp unique with ⟨apart, unique⟩
    by_cases found : (key == query) = true
    · have absent : ∀ other ∈ keys, (other == query) = false := by
        intro other member
        apply Bool.eq_false_iff.mpr
        intro same
        have equal := BEq.trans found (BEq.symm same)
        rw [apart other member] at equal
        contradiction
      have filtered : keys.filter (fun key => !(key == query)) = keys :=
        List.filter_eq_self.mpr (fun other member => by simp [absent other member])
      simp [found, filtered]
    · have count := ih unique
      simp [found]
      omega

private theorem has_eq_any [BEq κ] (entries : List (κ × υ)) (query : κ) :
    (MapEntries.get entries query).isSome = (entries.map Prod.fst).any (· == query) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    by_cases found : (key == query) = true <;> simp [MapEntries.get, found, ih]

theorem JSMap.size_delete [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) :
    (m.delete key).size = if m.has key then m.size - 1 else m.size := by
  have count := filter_length m.keys key m.unique
  have observed : m.keys.any (· == key) = m.has key := (has_eq_any m.entries key).symm
  have lengths : (m.keys.filter (fun query => !(query == key))).length = (m.delete key).size := by
    rw [← JSMap.keys_delete]
    simp [keys, size]
  rw [lengths, observed] at count
  have original : m.keys.length = m.size := by simp [keys, size]
  rw [original] at count
  cases h : m.has key <;> simp [h] at count ⊢ <;> omega

theorem JSSet.size_delete [BEq κ] [EquivBEq κ] (s : JSSet κ) (key : κ) :
    (s.delete key).size = if s.has key then s.size - 1 else s.size := by
  cases s with
  | mk m => exact JSMap.size_delete m key

theorem JSMap.has_set [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key query : κ) (value : υ) :
    (m.set key value).has query = ((key == query) || m.has query) := by
  simp only [has, get_set]
  split <;> simp_all

theorem JSMap.has_delete [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key query : κ) :
    (m.delete key).has query = (!(key == query) && m.has query) := by
  simp only [has, get_delete]
  split <;> simp_all

theorem NumberMap.size_delete (m : NumberMap υ) (key : Float.Model) :
    NumberMap.size (NumberMap.delete m key) = if NumberMap.has m key then NumberMap.size m - 1 else NumberMap.size m :=
  @JSMap.size_delete _ _ NumberKey.equality NumberKey.equiv m key

theorem NumberSet.size_delete (s : NumberSet) (key : Float.Model) :
    NumberSet.size (NumberSet.delete s key) = if NumberSet.has s key then NumberSet.size s - 1 else NumberSet.size s :=
  @JSSet.size_delete _ NumberKey.equality NumberKey.equiv s key

end Ariadne.Shallow

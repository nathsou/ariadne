import Ariadne.Model.Eval

/-!
# Maps

A class's `Map` field denotes an association list: `mapGet` finds a key, `mapPut` replaces its value
in place or adds it last, `mapDel` removes it. What a lookup sees after an update:
-/

namespace Ariadne

theorem mapGet_nil {α : Type} (k : JSString) : mapGet ([] : List (JSString × α)) k = none := rfl

theorem mapGet_mapPut {α : Type} : ∀ (m : List (JSString × α)) (k j : JSString) (v : α),
    mapGet (mapPut m k v) j = if j = k then some v else mapGet m j
  | [], k, j, v => by by_cases h : j = k <;> simp [mapPut, mapGet, List.lookup, h, beq_eq_false_iff_ne.mpr]
  | (k', w) :: rest, k, j, v => by
    by_cases hk : k' = k
    · subst hk
      by_cases hj : j = k'
      · subst hj; simp [mapPut, mapGet]
      · simp [mapPut, mapGet, List.lookup, hj, beq_eq_false_iff_ne.mpr hj]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [mapPut, hk', Bool.false_eq_true, ite_false]
      have ih := mapGet_mapPut rest k j v
      simp only [mapGet] at ih ⊢
      by_cases hj : j = k'
      · subst hj; simp [List.lookup, hk]
      · simp [List.lookup, beq_eq_false_iff_ne.mpr hj, ih]

theorem mapGet_mapDel {α : Type} : ∀ (m : List (JSString × α)) (k j : JSString),
    mapGet (mapDel m k) j = if j = k then none else mapGet m j
  | [], k, j => by simp [mapDel, mapGet]
  | (k', w) :: rest, k, j => by
    have ih := mapGet_mapDel rest k j
    simp only [mapDel, mapGet] at ih ⊢
    by_cases hk : k' = k
    · subst hk
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false, ih]
      by_cases hj : j = k'
      · simp [hj]
      · simp [hj, List.lookup, beq_eq_false_iff_ne.mpr hj]
    · have : (k' != k) = true := bne_iff_ne.mpr hk
      simp only [List.filter_cons, this, ite_true, List.lookup]
      by_cases hj : j = k'
      · subst hj; simp [hk]
      · simp [beq_eq_false_iff_ne.mpr hj, ih]

theorem mapPut_mapPut {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v w : α),
    mapPut (mapPut m k v) k w = mapPut m k w
  | [], k, v, w => by simp [mapPut]
  | (k', x) :: rest, k, v, w => by
    by_cases hk : k' = k
    · subst hk; simp [mapPut]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp [mapPut, hk', mapPut_mapPut rest k v w]

/-! ## Keys -/

theorem mapGet_isSome_iff {α : Type} (m : List (JSString × α)) (k : JSString) :
    (mapGet m k).isSome ↔ k ∈ m.map (·.1) := by
  induction m with
  | nil => simp [mapGet]
  | cons e rest ih =>
    obtain ⟨k', v⟩ := e
    simp only [mapGet, List.lookup] at ih ⊢
    by_cases h : k = k'
    · subst h; simp
    · simp [beq_eq_false_iff_ne.mpr h, ih, h]

/-- Setting a key already present leaves the keys as they were. -/
theorem mapPut_keys_of_mem {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v : α),
    k ∈ m.map (·.1) → (mapPut m k v).map (·.1) = m.map (·.1)
  | [], _, _, h => by simp at h
  | (k', w) :: rest, k, v, h => by
    by_cases hk : k' = k
    · subst hk; simp [mapPut]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      have : k ∈ rest.map (·.1) := by simp only [List.map_cons, List.mem_cons] at h; rcases h with h | h <;> simp_all
      simp [mapPut, hk', mapPut_keys_of_mem rest k v this]

/-- Setting a key adds at most that key. -/
theorem mem_mapPut_keys {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v : α) (x : JSString),
    x ∈ (mapPut m k v).map (·.1) → x = k ∨ x ∈ m.map (·.1)
  | [], _, _, _, h => by simp [mapPut] at h; exact .inl h
  | (k', w) :: rest, k, v, x, h => by
    by_cases hk : k' = k
    · subst hk; simp only [mapPut, beq_self_eq_true, ite_true, List.map_cons, List.mem_cons] at h
      rcases h with h | h <;> simp [h]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [mapPut, hk', Bool.false_eq_true, ite_false, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact .inr (by simp [h])
      · rcases mem_mapPut_keys rest k v x h with h | h
        · exact .inl h
        · exact .inr (by simp [h])

/-- Setting a key keeps the keys distinct. -/
theorem mapPut_keys_nodup {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v : α),
    (m.map (·.1)).Nodup → ((mapPut m k v).map (·.1)).Nodup
  | [], _, _, _ => by simp [mapPut]
  | (k', w) :: rest, k, v, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases hk : k' = k
    · subst hk; simp [mapPut, h.1, h.2]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [mapPut, hk', Bool.false_eq_true, ite_false, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, mapPut_keys_nodup rest k v h.2⟩
      rcases mem_mapPut_keys rest k v k' hm with e | e
      · exact hk e
      · exact h.1 e

theorem mem_mapDel_keys {α : Type} (m : List (JSString × α)) (k x : JSString) :
    x ∈ (mapDel m k).map (·.1) → x ∈ m.map (·.1) := by
  simp only [mapDel, List.mem_map, List.mem_filter]
  rintro ⟨e, ⟨he, _⟩, rfl⟩; exact ⟨e, he, rfl⟩

theorem mapDel_keys_nodup {α : Type} (m : List (JSString × α)) (k : JSString) :
    (m.map (·.1)).Nodup → ((mapDel m k).map (·.1)).Nodup :=
  fun h => h.sublist (List.filter_sublist.map _)

/-- Distinct keys among some given ones are at most as many. -/
theorem length_le_of_keys {α : Type} {m : List (JSString × α)} {K : List JSString} (hn : (m.map (·.1)).Nodup)
    (hk : ∀ x ∈ m.map (·.1), x ∈ K) : m.length ≤ K.length := by
  have := hn.length_le_of_subset hk
  simpa using this

theorem length_mapPut_le {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v : α),
    (mapPut m k v).length ≤ m.length + 1
  | [], _, _ => by simp [mapPut]
  | (k', w) :: rest, k, v => by
    by_cases hk : k' = k
    · subst hk; simp [mapPut]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [mapPut, hk', Bool.false_eq_true, ite_false, List.length_cons]
      have := length_mapPut_le rest k v
      omega

end Ariadne

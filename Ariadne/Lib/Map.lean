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

end Ariadne

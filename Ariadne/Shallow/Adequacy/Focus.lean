import Ariadne.Shallow.Adequacy.Array
import Ariadne.Shallow.Adequacy.Map

namespace Ariadne.Shallow.DataRelation
open Heap

/-- Select one represented element, and retain the frame needed to rebuild
its container after mutation of that element. Runtime references are retained;
the native element is replaced by the updated value. -/
theorem Elements.focus {element : DataRelation runtime native} {heap : Heap}
    {values : List runtime} {natives : List native} {footprint : Footprint}
    (related : Elements element heap values natives footprint) (index : Nat)
    (old : native) (found : natives[index]? = some old) :
    ∃ value selected,
      values[index]? = some value ∧ selected ⊆ footprint ∧
      element.Holds heap value old selected ∧
      ∀ (after : Heap) (updated : native), element.Holds after value updated selected →
        Modifies selected heap after → Elements element after values (natives.set index updated) footprint := by
  induction related generalizing index with
  | nil => simp at found
  | @cons value head headFootprint values natives tailFootprint headRelated tailRelated separate ih =>
    cases index with
    | zero =>
      have equal : old = head := by simpa using found.symm
      subst old
      refine ⟨value, headFootprint, rfl, (by simp), headRelated, ?_⟩
      intro after updated update writes
      have framed := tailRelated.frame (writes.frame tailRelated.allocated separate.symm)
      simpa only [List.set_cons_zero] using Elements.cons update framed separate
    | succ index =>
      have tailFound : natives[index]? = some old := by simpa using found
      obtain ⟨selectedValue, selectedFootprint, runtimeFound, subset, selected, rebuild⟩ := ih index tailFound
      refine ⟨selectedValue, selectedFootprint, (by simpa using runtimeFound),
        (fun address member => List.mem_append_right _ (subset member)), selected, ?_⟩
      intro after updated update writes
      have headSeparate : Disjoint headFootprint selectedFootprint :=
        fun address member selected => separate address member (subset selected)
      have framed := element.frame headRelated (writes.frame (element.allocated headRelated) headSeparate)
      simpa only [List.set_cons_succ] using Elements.cons framed (rebuild after updated update writes) separate

/-- Map-key selection retains the stored key, order and runtime value reference.
Only the selected native value is replaced. Scalar keys need no heap framing. -/
theorem Elements.focusKey [BEq key] {codec : Value → key → Prop} {element : DataRelation Value native}
    {heap : Heap} {entries : List (Value × Value)} {natives : List (key × native)} {footprint : Footprint}
    (related : Elements ((DataRelation.scalar codec).product element) heap entries natives footprint)
    (query : key) (sourceQuery : Value) (old : native)
    (found : MapEntries.get natives query = some old)
    (keys : ∀ {source native}, codec source native → sameValueZero source sourceQuery = (native == query)) :
    ∃ value selected,
      mapGet entries sourceQuery = value ∧ selected ⊆ footprint ∧ element.Holds heap value old selected ∧
      ∀ (after : Heap) (updated : native), element.Holds after value updated selected →
        Modifies selected heap after →
          Elements ((DataRelation.scalar codec).product element) after entries
            (MapEntries.set natives query updated) footprint := by
  induction related with
  | nil => simp [MapEntries.get] at found
  | @cons pair native head entries natives tail pairRelated tailRelated separate ih =>
    rcases pair with ⟨sourceKey, sourceValue⟩
    rcases native with ⟨nativeKey, nativeValue⟩
    obtain ⟨keyFootprint, valueFootprint, keyRelated, valueRelated, _, headEq⟩ := pairRelated
    obtain ⟨keyEncoded, rfl⟩ := keyRelated
    simp only [List.nil_append] at headEq
    subst head
    have same := keys keyEncoded
    by_cases foundKey : (nativeKey == query) = true
    · have equal : old = nativeValue := by simpa [MapEntries.get, foundKey] using found.symm
      subst old
      refine ⟨sourceValue, valueFootprint, (by simp [mapGet, same, foundKey]), (by simp), valueRelated, ?_⟩
      intro after updated update writes
      have pairUpdate : ((DataRelation.scalar codec).product element).Holds after
          (sourceKey, sourceValue) (nativeKey, updated) valueFootprint :=
        ⟨[], valueFootprint, ⟨keyEncoded, rfl⟩, update, (by simp [Disjoint]), rfl⟩
      have framed := tailRelated.frame (writes.frame tailRelated.allocated separate.symm)
      simpa only [MapEntries.set, foundKey, ↓reduceIte] using Elements.cons pairUpdate framed separate
    · have remaining : MapEntries.get natives query = some old := by simpa [MapEntries.get, foundKey] using found
      obtain ⟨value, selected, runtimeFound, subset, represented, rebuild⟩ := ih remaining
      refine ⟨value, selected, (by simpa [mapGet, same, foundKey] using runtimeFound),
        (fun address member => List.mem_append_right _ (subset member)), represented, ?_⟩
      intro after updated update writes
      have headSeparate : Disjoint valueFootprint selected :=
        fun address member selected => separate address member (subset selected)
      have framed := element.frame valueRelated (writes.frame (element.allocated valueRelated) headSeparate)
      have pairFrame : ((DataRelation.scalar codec).product element).Holds after
          (sourceKey, sourceValue) (nativeKey, nativeValue) valueFootprint :=
        ⟨[], valueFootprint, ⟨keyEncoded, rfl⟩, framed, (by simp [Disjoint]), rfl⟩
      simpa only [MapEntries.set, foundKey, Bool.false_eq_true, ↓reduceIte] using
        Elements.cons pairFrame (rebuild after updated update writes) separate

end Ariadne.Shallow.DataRelation

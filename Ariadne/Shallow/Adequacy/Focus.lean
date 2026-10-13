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

/-- Distinct positions in an owned container select disjoint element
footprints. This is the heap consequence of a passing index guard. -/
theorem Elements.focus_disjoint {element : DataRelation runtime native} {heap : Heap}
    {values : List runtime} {natives : List native} {footprint : Footprint}
    (related : Elements element heap values natives footprint) (left right : Nat)
    (a b : native) (foundLeft : natives[left]? = some a) (foundRight : natives[right]? = some b)
    (different : left ≠ right) :
    ∃ first second firstFootprint secondFootprint,
      values[left]? = some first ∧ values[right]? = some second ∧
      firstFootprint ⊆ footprint ∧ secondFootprint ⊆ footprint ∧
      element.Holds heap first a firstFootprint ∧ element.Holds heap second b secondFootprint ∧
      Disjoint firstFootprint secondFootprint := by
  induction related generalizing left right with
  | nil => simp at foundLeft
  | @cons value head headFootprint values natives tailFootprint headRelated tailRelated separate ih =>
    cases left with
    | zero =>
      cases right with
      | zero => exact False.elim (different rfl)
      | succ right =>
        have equal : a = head := by simpa using foundLeft.symm
        subst a
        obtain ⟨second, selected, lookup, subset, selectedRelated, _⟩ :=
          tailRelated.focus right b (by simpa using foundRight)
        exact ⟨value, second, headFootprint, selected, rfl, by simpa using lookup,
          by simp, fun _ member => List.mem_append_right _ (subset member),
          headRelated, selectedRelated, fun address member other => separate address member (subset other)⟩
    | succ left =>
      cases right with
      | zero =>
        have equal : b = head := by simpa using foundRight.symm
        subst b
        obtain ⟨first, selected, lookup, subset, selectedRelated, _⟩ :=
          tailRelated.focus left a (by simpa using foundLeft)
        exact ⟨first, value, selected, headFootprint, by simpa using lookup, rfl,
          (fun _ member => List.mem_append_right _ (subset member)), by simp,
          selectedRelated, headRelated,
          fun address member other => separate address other (subset member)⟩
      | succ right =>
        obtain ⟨first, second, fa, fb, ha, hb, sa, sb, ra, rb, split⟩ :=
          ih left right (by simpa using foundLeft) (by simpa using foundRight)
            (fun same => different (congrArg Nat.succ same))
        exact ⟨first, second, fa, fb, by simpa using ha, by simpa using hb,
          (fun _ member => List.mem_append_right _ (sa member)),
          (fun _ member => List.mem_append_right _ (sb member)), ra, rb, split⟩

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

/-- Two scalar keys whose equality classes cannot overlap select disjoint
value footprints. Expressing the guard in the map's key equality also covers
SameValueZero keys, for which JavaScript strict inequality is insufficient. -/
theorem Elements.focusKey_disjoint [BEq key]
    {codec : Value → key → Prop} {element : DataRelation Value native}
    {heap : Heap} {entries : List (Value × Value)} {natives : List (key × native)}
    {footprint : Footprint}
    (related : Elements ((DataRelation.scalar codec).product element) heap entries natives footprint)
    (left right : key) (sourceLeft sourceRight : Value) (a b : native)
    (foundLeft : MapEntries.get natives left = some a)
    (foundRight : MapEntries.get natives right = some b)
    (keysLeft : ∀ {source native}, codec source native →
      sameValueZero source sourceLeft = (native == left))
    (keysRight : ∀ {source native}, codec source native →
      sameValueZero source sourceRight = (native == right))
    (different : ∀ candidate, (candidate == left) = true →
      (candidate == right) = true → False) :
    ∃ first second firstFootprint secondFootprint,
      mapGet entries sourceLeft = first ∧ mapGet entries sourceRight = second ∧
      firstFootprint ⊆ footprint ∧ secondFootprint ⊆ footprint ∧
      element.Holds heap first a firstFootprint ∧ element.Holds heap second b secondFootprint ∧
      Disjoint firstFootprint secondFootprint := by
  induction related with
  | nil => simp [MapEntries.get] at foundLeft
  | @cons pair native head entries natives tail pairRelated tailRelated separate ih =>
    rcases pair with ⟨sourceKey, sourceValue⟩
    rcases native with ⟨nativeKey, nativeValue⟩
    obtain ⟨keyFootprint, valueFootprint, keyRelated, valueRelated, _, headEq⟩ := pairRelated
    obtain ⟨keyEncoded, rfl⟩ := keyRelated
    simp only [List.nil_append] at headEq
    subst head
    have sameLeft := keysLeft keyEncoded
    have sameRight := keysRight keyEncoded
    by_cases atLeft : (nativeKey == left) = true
    · have atRight : (nativeKey == right) ≠ true := different nativeKey atLeft
      have equal : a = nativeValue := by
        simpa [MapEntries.get, atLeft] using foundLeft.symm
      subst a
      obtain ⟨second, selected, lookup, subset, selectedRelated, _⟩ :=
        tailRelated.focusKey right sourceRight b
          (by simpa [MapEntries.get, atRight] using foundRight) keysRight
      exact ⟨sourceValue, second, valueFootprint, selected,
        by simp [mapGet, sameLeft, atLeft],
        by simpa [mapGet, sameRight, atRight] using lookup,
        by simp, (fun _ member => List.mem_append_right _ (subset member)),
        valueRelated, selectedRelated,
        fun address member other => separate address member (subset other)⟩
    · by_cases atRight : (nativeKey == right) = true
      · have equal : b = nativeValue := by
          simpa [MapEntries.get, atRight] using foundRight.symm
        subst b
        obtain ⟨first, selected, lookup, subset, selectedRelated, _⟩ :=
          tailRelated.focusKey left sourceLeft a
            (by simpa [MapEntries.get, atLeft] using foundLeft) keysLeft
        exact ⟨first, sourceValue, selected, valueFootprint,
          by simpa [mapGet, sameLeft, atLeft] using lookup,
          by simp [mapGet, sameRight, atRight],
          (fun _ member => List.mem_append_right _ (subset member)), by simp,
          selectedRelated, valueRelated,
          fun address member other => separate address other (subset member)⟩
      · obtain ⟨first, second, fa, fb, ha, hb, sa, sb, ra, rb, split⟩ :=
          ih (by simpa [MapEntries.get, atLeft] using foundLeft)
            (by simpa [MapEntries.get, atRight] using foundRight)
        exact ⟨first, second, fa, fb,
          by simpa [mapGet, sameLeft, atLeft] using ha,
          by simpa [mapGet, sameRight, atRight] using hb,
          (fun _ member => List.mem_append_right _ (sa member)),
          (fun _ member => List.mem_append_right _ (sb member)), ra, rb, split⟩

end Ariadne.Shallow.DataRelation

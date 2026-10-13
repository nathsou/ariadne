import Examples.ReferenceSource.Tree

/-!
# The tree layout is the generated representation

`layout` is the data relation the extractor's representation combinators give
the tree's state: an instance whose `parents` field is a scalar map and whose
`children` field maps strings to owned string arrays. Owning those arrays means
their footprints are disjoint, so the relation holds exactly when the concrete
`Layout` used by the source proofs does.
-/

namespace Examples.ReferenceSource.Tree
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_tree.Shallow
open Heap DataRelation

def layout : DataRelation Value State' :=
  ((field "parents" (map string string)
    (field "children" (map string (array string)) fieldsNil)).classState "Tree").comap NativeDestruct.«Tree#state»

/-- The addresses of the child-list arrays, read off the children map's entries. -/
def refsOf (enc : List (Value × Value)) : List Nat :=
  enc.map fun kv => match kv.2 with
    | .ref a => a
    | _ => 0

theorem strings_iff {heap : Heap} {values : List Value} {natives : List JSString} {footprint : Footprint} :
    Elements string heap values natives footprint ↔ values = natives.map .string ∧ footprint = [] := by
  constructor
  · intro h
    induction h with
    | nil => simp
    | cons head _ _ ih =>
      simp only [DataRelation.string, DataRelation.scalar] at head
      obtain ⟨rfl, rfl⟩ := head
      obtain ⟨rfl, rfl⟩ := ih
      simp
  · rintro ⟨rfl, rfl⟩
    induction natives with
    | nil => exact .nil
    | cons x xs ih =>
      exact .cons (show string.Holds heap (.string x) x [] by simp [DataRelation.string, DataRelation.scalar]) ih
        (by simp [Disjoint])

theorem array_string_iff {heap : Heap} {value : Value} {native : List JSString} {footprint : Footprint} :
    (array string).Holds heap value native footprint ↔
      native.length < 4294967296 ∧ ∃ a, value = .ref a ∧ heap[a]? = some (.array (native.map .string)) ∧
        footprint = [a] := by
  constructor
  · rintro ⟨short, a, object, children, rfl, lookup, ⟨values, project, related⟩, _, rfl⟩
    cases object
    all_goals try simp at project
    case array xs =>
      cases project
      obtain ⟨rfl, rfl⟩ := strings_iff.mp related
      exact ⟨short, a, rfl, lookup, rfl⟩
  · rintro ⟨short, a, rfl, lookup, rfl⟩
    exact ⟨short, a, _, [], rfl, lookup, ⟨_, rfl, strings_iff.mpr ⟨rfl, rfl⟩⟩, by simp, rfl⟩

/-- Owned child lists: the entry relation is `Children` with distinct arrays outside the maps. -/
theorem children_iff {heap : Heap} {pA cA : Nat} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)} {footprint : Footprint},
      pA ∉ footprint → cA ∉ footprint →
      (Elements (string.product (array string)) heap enc es footprint ↔
        Children heap pA cA enc es ∧ (enc.map Prod.snd).Nodup ∧ (∀ e ∈ es, e.2.length < 4294967296) ∧
          footprint = refsOf enc)
  | [], [], footprint, _, _ => by
    constructor
    · intro h; cases h; simp [Children, refsOf]
    · rintro ⟨-, -, -, rfl⟩; exact .nil
  | [], _ :: _, footprint, _, _ => by
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; exact h.elim
  | _ :: _, [], footprint, _, _ => by
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; exact h.elim
  | (k, v) :: enc, (ek, ev) :: es, footprint, np, nc => by
    constructor
    · intro h
      cases h with
      | cons head rest separate =>
        rename_i fh ft
        obtain ⟨fk, fv, key, value, _, rfl⟩ := head
        simp only [DataRelation.string, DataRelation.scalar] at key
        obtain ⟨rfl, rfl⟩ := key
        obtain ⟨short, a, rfl, lookup, rfl⟩ := array_string_iff.mp value
        simp only [List.nil_append, List.mem_cons, not_or, List.cons_append] at np nc
        obtain ⟨c, nodup, lengths, rfl⟩ := (children_iff np.2 nc.2).mp rest
        have fresh : a ∉ refsOf enc := by simpa [Disjoint] using separate
        refine ⟨⟨rfl, ⟨a, rfl, lookup, Ne.symm np.1, Ne.symm nc.1⟩, c⟩, ?_, ?_, rfl⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨fun member => fresh ?_, nodup⟩
          simp only [refsOf, List.mem_map]
          obtain ⟨kv, mem, same⟩ := List.mem_map.mp member
          exact ⟨kv, mem, by simp [same]⟩
        · intro e member
          rcases List.mem_cons.mp member with rfl | member
          · exact short
          · exact lengths e member
    · rintro ⟨⟨key, ⟨a, value, lookup, na, nc'⟩, c⟩, nodup, lengths, rfl⟩
      simp only at key value
      subst key value
      simp only [refsOf, List.map_cons, List.mem_cons, not_or] at np nc
      have rest := (children_iff (footprint := refsOf enc) np.2 nc.2).mpr
        ⟨c, (List.nodup_cons.mp nodup).2, fun e member => lengths e (List.mem_cons_of_mem _ member), rfl⟩
      have short := lengths (ek, ev) (List.mem_cons_self ..)
      refine .cons (show (string.product (array string)).Holds heap (.string ek, .ref a) (ek, ev) ([] ++ [a]) from
        ⟨[], [a], by simp [DataRelation.string, DataRelation.scalar], array_string_iff.mpr ⟨short, a, rfl, lookup, rfl⟩,
          by simp [Disjoint], rfl⟩) rest ?_
      simp only [Disjoint]
      intro m hm member
      simp only [List.nil_append, List.mem_singleton] at hm
      subst hm
      apply (List.nodup_cons.mp nodup).1
      obtain ⟨kv, mem, same⟩ := List.mem_map.mp member
      obtain ⟨b, hb⟩ : ∃ b, kv.2 = .ref b := by
        obtain ⟨b, hb, -⟩ := c.refs kv.2 (List.mem_map.mpr ⟨kv, mem, rfl⟩)
        exact ⟨b, hb⟩
      simp only [hb] at same
      subst same
      exact List.mem_map.mpr ⟨kv, mem, hb⟩

theorem Children.notMaps {heap : Heap} {pA cA : Nat} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → ∀ a ∈ refsOf enc, a ≠ pA ∧ a ≠ cA
  | [], [], _ => by simp [refsOf]
  | (k, v) :: enc, _ :: _, ⟨_, ⟨b, value, _, np, nc⟩, rest⟩ => by
    intro a member
    simp only [refsOf, List.map_cons, List.mem_cons] at member
    simp only at value
    subst value
    rcases member with rfl | member
    · exact ⟨np, nc⟩
    · exact Children.notMaps rest a member

theorem ref_mem_refsOf {enc : List (Value × Value)} {heap : Heap} {pA cA : Nat} {es : List (JSString × List JSString)}
    (c : Children heap pA cA enc es) (a : Nat) : a ∈ refsOf enc ↔ .ref a ∈ enc.map Prod.snd := by
  constructor
  · intro member
    obtain ⟨kv, mem, same⟩ := List.mem_map.mp member
    obtain ⟨b, hb, -⟩ := c.refs kv.2 (List.mem_map.mpr ⟨kv, mem, rfl⟩)
    simp only [hb] at same
    subst same
    exact List.mem_map.mpr ⟨kv, mem, hb⟩
  · intro member
    obtain ⟨kv, mem, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨kv, mem, by simp [same]⟩

/-- **The source layout is the generated representation.** An instance whose
fields are exactly the two maps represents a native tree under the generated
relation if and only if the concrete layout holds; the instance then owns the
two maps and every child-list array. -/
theorem layout_iff {heap : Heap} {address pA cA : Nat} {native : State'} {owned : Footprint}
    (fields : heap[address]? = some (.instance_ "Tree" [("parents", .ref pA), ("children", .ref cA)])) :
    layout.Holds heap (.ref address) native owned ↔
      Layout heap address native pA cA ∧
        ∃ enc, heap[cA]? = some (.map enc) ∧ owned = address :: pA :: cA :: refsOf enc := by
  constructor
  · rintro ⟨root, object, children, same, lookup, ⟨values, project, related⟩, fresh, rfl⟩
    cases same
    rw [fields] at lookup
    cases lookup
    simp only [ite_true, Option.some.injEq] at project
    subst project
    obtain ⟨pv, pLookup, fp, rest, pHolds, restHolds, pSep, rfl⟩ := related
    obtain ⟨cv, cLookup, fc, nil, cHolds, nilHolds, cSep, rfl⟩ := restHolds
    obtain rfl : pv = .ref pA := by
      have h : List.lookup "parents" [("parents", Value.ref pA), ("children", Value.ref cA)] = some (.ref pA) := rfl
      rw [h] at pLookup; exact (Option.some.inj pLookup).symm
    obtain rfl : cv = .ref cA := by
      have h : List.lookup "children" [("parents", Value.ref pA), ("children", Value.ref cA)] = some (.ref cA) := rfl
      rw [h] at cLookup; exact (Option.some.inj cLookup).symm
    obtain ⟨_, rfl⟩ := nilHolds
    have pMap := map_scalar_iff (heap := heap) (source := .ref pA)
      (native := (NativeDestruct.«Tree#state» native).1) (footprint := fp) ScalarCodec.string ScalarCodec.string
    simp only [ScalarCodec.string, and_self, implies_true, true_and] at pMap
    obtain ⟨pA', same, pLookup, rfl⟩ := pMap.mp pHolds
    cases same
    obtain ⟨cA', object, children', same, cLookup, ⟨enc, cProject, elements⟩, cFresh, rfl⟩ := cHolds
    cases same
    have hobj : object = .map enc := by cases object <;> simp_all
    subst hobj
    have pc := pSep pA (by simp)
    simp only [List.append_nil, List.mem_cons, not_or] at pc
    have fresh' := fresh
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, or_false,
      List.append_nil] at fresh'
    obtain ⟨c, nodup, lengths, rfl⟩ := (children_iff pc.2 cFresh).mp elements
    refine ⟨⟨fields, pLookup, ⟨enc, cLookup, c⟩, ⟨pc.1, fresh'.1, fresh'.2.1⟩,
      fun enc' h => ?_, lengths⟩, enc, cLookup, by simp⟩
    rw [cLookup] at h
    cases h
    exact ⟨nodup, fun member => fresh'.2.2 ((ref_mem_refsOf c address).mpr member)⟩
  · rintro ⟨l, enc, cLookup, rfl⟩
    obtain ⟨d1, d2, d3⟩ := l.distinct
    obtain ⟨enc', cLookup', c⟩ := l.childrenMap
    rw [cLookup] at cLookup'
    cases cLookup'
    obtain ⟨nodup, notSelf⟩ := l.unique enc cLookup
    have pFresh : pA ∉ refsOf enc := fun member => (c.notMaps pA member).1 rfl
    have cFresh : cA ∉ refsOf enc := fun member => (c.notMaps cA member).2 rfl
    have aFresh : address ∉ refsOf enc := fun member => notSelf ((ref_mem_refsOf c address).mp member)
    refine ⟨address, _, pA :: cA :: refsOf enc, rfl, fields, ⟨[("parents", .ref pA), ("children", .ref cA)], by simp, ?_⟩, ?_, rfl⟩
    · refine ⟨.ref pA, by simp, [pA], cA :: refsOf enc, ?_, ⟨.ref cA, rfl, cA :: refsOf enc, [], ?_,
        ⟨trivial, rfl⟩, by simp [Disjoint], by simp⟩, ?_, rfl⟩
      · have pMap := map_scalar_iff (heap := heap) (source := .ref pA)
          (native := (NativeDestruct.«Tree#state» native).1) (footprint := [pA]) ScalarCodec.string ScalarCodec.string
        simp only [ScalarCodec.string, and_self, implies_true, true_and] at pMap
        exact pMap.mpr ⟨pA, rfl, by simpa [NativeDestruct.«Tree#state», stringStrings] using l.parentsMap, rfl⟩
      · refine ⟨cA, .map enc, refsOf enc, rfl, cLookup, ⟨enc, rfl, ?_⟩, cFresh, rfl⟩
        simp only [NativeDestruct.«Tree#state»]
        exact (children_iff pFresh cFresh).mpr ⟨c, nodup, l.lengths, rfl⟩
      · simp [Disjoint, d1, pFresh]
    · simp [d2, d3, aFresh]

theorem Layout.represents {heap : Heap} {address pA cA : Nat} {native : State'}
    (l : Layout heap address native pA cA) : Represents layout heap (.ref address) native := by
  obtain ⟨enc, cLookup, _⟩ := l.childrenMap
  exact ⟨_, (layout_iff l.instance_).mpr ⟨l, enc, cLookup, rfl⟩⟩

/-- **Traces, in the generated representation.** After `new Tree()` and any
sequence of operations within limits, the source instance represents the
emitted state under the extractor's relation for the tree's state. -/
theorem trace_represents (before : Ariadne.State) (span : Span) (ops : List Operation)
    (runs : Runs «Tree##new» ops) :
    let address := before.heap.length + 2
    ∃ fresh after,
      SourceEvaluates Extracted_reference_tree.source before (.newClass "Tree" [] span) (.ref address) fresh ∧
      SourceTrace Extracted_reference_tree.source fresh (ops.map (call address)) (ops.map fun _ => .undefined) after ∧
      Represents layout after.heap (.ref address) (ops.foldl applyOp «Tree##new») := by
  intro address
  obtain ⟨fresh, constructed, layout⟩ := new_source before span
  obtain ⟨after, trace, final⟩ := trace_source fresh address _ _ _ ops runs layout
  exact ⟨fresh, after, constructed, trace, final.represents⟩

end Examples.ReferenceSource.Tree

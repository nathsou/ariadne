import Ariadne.Shallow.Represents
import Ariadne.SourceFrom

/-!
Maps whose keys and values are scalars own exactly one heap object. Their
representation is an equation: the object holds the encoded native entries. Map
reads, writes and deletions on encoded entries are the native operations.
-/

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

def encodeEntries (key : κ → Value) (value : υ → Value) (xs : List (κ × υ)) : List (Value × Value) :=
  xs.map fun entry => (key entry.1, value entry.2)

/-- Scalar codecs given by an encoding function and a validity condition. -/
structure ScalarCodec (κ : Type) where
  encode : κ → Value
  valid : κ → Prop
  relation : DataRelation Value κ
  holds : ∀ {heap value native footprint}, relation.Holds heap value native footprint ↔
    (valid native ∧ value = encode native) ∧ footprint = []

def ScalarCodec.string : ScalarCodec JSString where
  encode := .string
  valid := fun _ => True
  relation := DataRelation.string
  holds := by intros; simp [DataRelation.string, DataRelation.scalar]

def ScalarCodec.int53 : ScalarCodec Int where
  encode := fun n => .number (Float.Model.ofInt n)
  valid := Int53.InRange
  relation := DataRelation.int53
  holds := by intros; simp [DataRelation.int53, DataRelation.scalar]

theorem elements_scalar_iff (key : ScalarCodec κ) (value : ScalarCodec υ) {heap : Heap}
    {entries : List (Value × Value)} {natives : List (κ × υ)} {footprint : Footprint} :
    Elements (key.relation.product value.relation) heap entries natives footprint ↔
      entries = encodeEntries key.encode value.encode natives ∧
      (∀ entry ∈ natives, key.valid entry.1 ∧ value.valid entry.2) ∧ footprint = [] := by
  constructor
  · intro h
    induction h with
    | nil => simp [encodeEntries]
    | @cons entry element head values natives tail pair rest separate ih =>
      rcases entry with ⟨ek, ev⟩
      obtain ⟨fl, fr, hk, hv, _, footprintEq⟩ := pair
      obtain ⟨⟨vk, ekEq⟩, flEq⟩ := key.holds.mp hk
      obtain ⟨⟨vv, evEq⟩, frEq⟩ := value.holds.mp hv
      obtain ⟨valuesEq, valid, tailEq⟩ := ih
      simp only at ekEq evEq
      subst ekEq evEq valuesEq tailEq flEq frEq footprintEq
      refine ⟨rfl, ?_, rfl⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨vk, vv⟩
      · exact valid entry member
  · rintro ⟨rfl, valid, rfl⟩
    induction natives with
    | nil => exact .nil
    | cons entry natives ih =>
      have head := valid entry (by simp)
      have pair : (key.relation.product value.relation).Holds heap
          (key.encode entry.1, value.encode entry.2) entry [] :=
        ⟨[], [], key.holds.mpr ⟨⟨head.1, rfl⟩, rfl⟩, value.holds.mpr ⟨⟨head.2, rfl⟩, rfl⟩,
          (by simp [Disjoint]), rfl⟩
      exact .cons pair (ih (fun e member => valid e (by simp [member]))) (by simp [Disjoint])

/-- A scalar map is one heap object holding its encoded entries. -/
theorem map_scalar_iff [BEq κ] (key : ScalarCodec κ) (value : ScalarCodec υ) {heap : Heap}
    {source : Value} {native : JSMap κ υ} {footprint : Footprint} :
    (DataRelation.map key.relation value.relation).Holds heap source native footprint ↔
      ∃ address, source = .ref address ∧
        heap[address]? = some (.map (encodeEntries key.encode value.encode native.entries)) ∧
        (∀ entry ∈ native.entries, key.valid entry.1 ∧ value.valid entry.2) ∧ footprint = [address] := by
  constructor
  · rintro ⟨address, object, children, rfl, lookup, ⟨entries, project, related⟩, _, rfl⟩
    cases object
    all_goals try contradiction
    case map actual =>
      cases project
      obtain ⟨rfl, valid, rfl⟩ := (elements_scalar_iff key value).mp related
      exact ⟨address, rfl, lookup, valid, rfl⟩
  · rintro ⟨address, rfl, lookup, valid, rfl⟩
    exact ⟨address, _, [], rfl, lookup, ⟨_, rfl, (elements_scalar_iff key value).mpr ⟨rfl, valid, rfl⟩⟩,
      (by simp), rfl⟩

theorem sameValueZero_string (a b : JSString) : sameValueZero (.string a) (.string b) = (a == b) := rfl

theorem mapGet_string (value : υ → Value) (xs : List (JSString × υ)) (k : JSString) :
    mapGet (encodeEntries .string value xs) (.string k) = ((MapEntries.get xs k).map value).getD .undefined := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    rcases entry with ⟨a, v⟩
    by_cases same : (a == k) = true
    · simp [mapGet, encodeEntries, MapEntries.get, sameValueZero_string, same]
    · simp only [encodeEntries, List.map_cons] at ih ⊢
      simp only [mapGet, List.find?_cons, sameValueZero_string, same, MapEntries.get] at ih ⊢
      exact ih

theorem mapHas_string (value : υ → Value) (xs : List (JSString × υ)) (k : JSString) :
    mapHas (encodeEntries .string value xs) (.string k) = (MapEntries.get xs k).isSome := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    rcases entry with ⟨a, v⟩
    by_cases same : (a == k) = true
    · simp [mapHas, encodeEntries, MapEntries.get, sameValueZero_string, same]
    · simp only [encodeEntries, List.map_cons] at ih ⊢
      simp only [mapHas, List.any_cons, sameValueZero_string, same, MapEntries.get, Bool.false_or] at ih ⊢
      exact ih

theorem mapSet_string (value : υ → Value) (xs : List (JSString × υ)) (k : JSString) (v : υ) :
    mapSet (encodeEntries .string value xs) (.string k) (value v) =
      encodeEntries .string value (MapEntries.set xs k v) := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    rcases entry with ⟨a, w⟩
    by_cases same : (a == k) = true
    · simp [mapSet, encodeEntries, MapEntries.set, sameValueZero_string, same]
    · simp only [encodeEntries, List.map_cons] at ih ⊢
      simp only [mapSet, sameValueZero_string, same, MapEntries.set, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      rw [ih]

theorem mapDelete_string (value : υ → Value) (xs : List (JSString × υ)) (k : JSString) :
    mapDelete (encodeEntries .string value xs) (.string k) = encodeEntries .string value (MapEntries.delete xs k) := by
  simp only [mapDelete, encodeEntries, MapEntries.delete, List.filter_map]
  congr 1

end Ariadne.Shallow.Adequacy

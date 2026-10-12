import Ariadne.Value

namespace Ariadne.Shallow

namespace MapEntries

def get [BEq κ] : List (κ × υ) → κ → Option υ
  | [], _ => none
  | (k, v) :: xs, key => if k == key then some v else get xs key

def set [BEq κ] : List (κ × υ) → κ → υ → List (κ × υ)
  | [], key, value => [(key, value)]
  | (k, v) :: xs, key, value =>
    if k == key then (k, value) :: xs else (k, v) :: set xs key value

def delete [BEq κ] (xs : List (κ × υ)) (key : κ) : List (κ × υ) :=
  xs.filter fun entry => !(entry.1 == key)

theorem get_set [BEq κ] [EquivBEq κ] (xs : List (κ × υ)) (key query : κ) (value : υ) :
    get (set xs key value) query = if key == query then some value else get xs query := by
  induction xs with
  | nil => simp [get, set]
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    by_cases hk : (k == key) = true
    · have he := BEq.congr_left (c := query) hk
      simp [set, get, hk, he]
      split <;> simp_all
    · by_cases hq : (key == query) = true
      · have he := BEq.congr_right (a := k) hq
        simp [set, get, hk, ← he, ih, hq]
      · simp [set, get, hk, hq, ih]

theorem get_delete [BEq κ] [EquivBEq κ] (xs : List (κ × υ)) (key query : κ) :
    get (delete xs key) query = if key == query then none else get xs query := by
  induction xs with
  | nil => simp [get, delete]
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    by_cases hk : (k == key) = true
    · have he := BEq.congr_left (c := query) hk
      simp [delete, get, hk, he] at *
      split <;> simp_all
    · by_cases hq : (key == query) = true
      · have he := BEq.congr_right (a := k) hq
        simp [delete, get, hk, ← he, hq] at *
        exact ih
      · simp [delete, get, hk, hq] at *
        split <;> simp_all

theorem key_mem_set [BEq κ] (xs : List (κ × υ)) (key : κ) (value : υ) (query : κ)
    (member : query ∈ (set xs key value).map Prod.fst) :
    query = key ∨ query ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simpa [set] using member
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    simp only [set] at member
    split at member
    · exact Or.inr (by simpa using member)
    · simp only [List.map_cons, List.mem_cons] at member
      rcases member with h | h
      · exact Or.inr (by simp [h])
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

def Unique [BEq κ] (xs : List (κ × υ)) : Prop :=
  (xs.map Prod.fst).Pairwise (fun a b => (a == b) = false)

theorem unique_set [BEq κ] (xs : List (κ × υ)) (key : κ) (value : υ) (valid : Unique xs) :
    Unique (set xs key value) := by
  induction xs with
  | nil => simp [Unique, set]
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    simp only [Unique, List.map_cons, List.pairwise_cons] at valid ⊢
    simp only [set]
    split
    · simpa only [List.map_cons, List.pairwise_cons] using valid
    · rename_i h
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih valid.2⟩
      intro query member
      rcases key_mem_set xs key value query member with rfl | old
      · exact Bool.eq_false_iff.mpr h
      · exact valid.1 query old

theorem unique_delete [BEq κ] (xs : List (κ × υ)) (key : κ) (valid : Unique xs) :
    Unique (delete xs key) := by
  exact List.Pairwise.sublist (List.filter_sublist.map _) valid

theorem keys_set [BEq κ] (xs : List (κ × υ)) (key : κ) (value : υ) :
    (set xs key value).map Prod.fst =
      if (get xs key).isSome then xs.map Prod.fst else xs.map Prod.fst ++ [key] := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : (k == key) = true
    · simp [set, get, h]
    · simp only [set, get, h, Bool.false_eq_true, ↓reduceIte, List.map_cons, ih]
      split <;> rfl

theorem set_idempotent [BEq κ] [EquivBEq κ] (xs : List (κ × υ)) (key : κ) (value : υ) :
    set (set xs key value) key value = set xs key value := by
  induction xs with
  | nil => simp [set]
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : (k == key) = true <;> simp [set, h, ih]

end MapEntries

/-- An insertion-ordered map with unique keys under the chosen key equivalence. -/
structure JSMap (κ υ : Type) [BEq κ] where
  entries : List (κ × υ)
  unique : MapEntries.Unique entries

namespace JSMap

def empty [BEq κ] : JSMap κ υ := ⟨[], by simp [MapEntries.Unique]⟩
def get [BEq κ] (m : JSMap κ υ) (key : κ) : Option υ := MapEntries.get m.entries key
def has [BEq κ] (m : JSMap κ υ) (key : κ) : Bool := (m.get key).isSome
def size [BEq κ] (m : JSMap κ υ) : Nat := m.entries.length
def set [BEq κ] (m : JSMap κ υ) (key : κ) (value : υ) : JSMap κ υ :=
  ⟨MapEntries.set m.entries key value, MapEntries.unique_set _ _ _ m.unique⟩
def delete [BEq κ] (m : JSMap κ υ) (key : κ) : JSMap κ υ :=
  ⟨MapEntries.delete m.entries key, MapEntries.unique_delete _ _ m.unique⟩
def keys [BEq κ] (m : JSMap κ υ) : List κ := m.entries.map Prod.fst
def values [BEq κ] (m : JSMap κ υ) : List υ := m.entries.map Prod.snd

/-- Observational equality deliberately excludes insertion-order observations. -/
def LookupEq [BEq κ] (a b : JSMap κ υ) : Prop := ∀ key, a.get key = b.get key

@[ext] theorem ext [BEq κ] {a b : JSMap κ υ} (h : a.entries = b.entries) : a = b := by
  cases a; cases b; cases h; rfl

@[simp] theorem get_empty [BEq κ] (key : κ) : (empty : JSMap κ υ).get key = none := rfl
@[simp] theorem get_set [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key query : κ) (value : υ) :
    (m.set key value).get query = if key == query then some value else m.get query :=
  MapEntries.get_set _ _ _ _
@[simp] theorem get_set_self [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    (m.set key value).get key = some value := by simp
@[simp] theorem get_delete [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key query : κ) :
    (m.delete key).get query = if key == query then none else m.get query :=
  MapEntries.get_delete _ _ _

theorem LookupEq.refl [BEq κ] (m : JSMap κ υ) : LookupEq m m := fun _ => rfl
theorem LookupEq.symm [BEq κ] {a b : JSMap κ υ} (h : LookupEq a b) : LookupEq b a :=
  fun k => (h k).symm
theorem LookupEq.trans [BEq κ] {a b c : JSMap κ υ} (h : LookupEq a b) (g : LookupEq b c) : LookupEq a c :=
  fun k => (h k).trans (g k)
theorem LookupEq.set [BEq κ] [EquivBEq κ] {a b : JSMap κ υ}
    (h : LookupEq a b) (key : κ) (value : υ) : LookupEq (a.set key value) (b.set key value) := by
  intro query
  simp only [get_set, h query]
theorem LookupEq.delete [BEq κ] [EquivBEq κ] {a b : JSMap κ υ}
    (h : LookupEq a b) (key : κ) : LookupEq (a.delete key) (b.delete key) := by
  intro query
  simp only [get_delete, h query]
theorem set_idempotent [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    LookupEq ((m.set key value).set key value) (m.set key value) := by
  intro query
  simp only [get_set]
  split <;> rfl

theorem set_idempotent_eq [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    (m.set key value).set key value = m.set key value :=
  ext (MapEntries.set_idempotent _ _ _)

theorem set_comm [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (a b : κ) (v w : υ)
    (distinct : (a == b) = false) : LookupEq ((m.set a v).set b w) ((m.set b w).set a v) := by
  intro query
  simp only [get_set]
  by_cases ha : (a == query) = true <;> by_cases hb : (b == query) = true
  · have h := BEq.trans ha (BEq.symm hb)
    simp_all
  all_goals simp [ha, hb]

@[simp] theorem has_set_self [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    (m.set key value).has key = true := by simp [has]

@[simp] theorem has_delete_self [BEq κ] [EquivBEq κ] (m : JSMap κ υ) (key : κ) :
    (m.delete key).has key = false := by simp [has]

theorem keys_set [BEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    (m.set key value).keys = if m.has key then m.keys else m.keys ++ [key] :=
  MapEntries.keys_set _ _ _

theorem size_set [BEq κ] (m : JSMap κ υ) (key : κ) (value : υ) :
    (m.set key value).size = if m.has key then m.size else m.size + 1 := by
  have h := congrArg List.length (keys_set m key value)
  simp only [keys, List.length_map] at h
  split at h <;> simp_all [size]

end JSMap
end Ariadne.Shallow

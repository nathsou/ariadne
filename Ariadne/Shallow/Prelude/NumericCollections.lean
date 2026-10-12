import Ariadne.Shallow.Prelude.NumberKey
import Ariadne.Shallow.Prelude.Set

namespace Ariadne.Shallow

/-- Number-keyed collections select SameValueZero explicitly. This never changes
the IEEE equality instance used by ordinary number operations. -/
abbrev NumberMap (υ : Type) := @JSMap Float.Model υ NumberKey.equality
abbrev NumberSet := @JSSet Float.Model NumberKey.equality

namespace NumberMap
variable {υ : Type}

def empty : NumberMap υ := @JSMap.empty _ _ NumberKey.equality
def get (m : NumberMap υ) (key : Float.Model) : Option υ :=
  @JSMap.get _ _ NumberKey.equality m key
def has (m : NumberMap υ) (key : Float.Model) : Bool := (get m key).isSome
def set (m : NumberMap υ) (key : Float.Model) (value : υ) : NumberMap υ :=
  @JSMap.set _ _ NumberKey.equality m (NumberKey.normalize key) value
def delete (m : NumberMap υ) (key : Float.Model) : NumberMap υ :=
  @JSMap.delete _ _ NumberKey.equality m key
def keys (m : NumberMap υ) : List Float.Model := @JSMap.keys _ _ NumberKey.equality m
def values (m : NumberMap υ) : List υ := @JSMap.values _ _ NumberKey.equality m
def entries (m : NumberMap υ) : List (Float.Model × υ) := @JSMap.entries _ _ NumberKey.equality m
def size (m : NumberMap υ) : Nat := @JSMap.size _ _ NumberKey.equality m

@[simp] theorem get_empty (key : Float.Model) : get (empty : NumberMap υ) key = none := rfl

@[simp] theorem get_set (m : NumberMap υ) (key query : Float.Model) (value : υ) :
    get (set m key value) query =
      if NumberKey.equal key query then some value else get m query := by
  rw [get, set, @JSMap.get_set _ _ NumberKey.equality NumberKey.equiv]
  change (if NumberKey.equal (NumberKey.normalize key) query then some value else get m query) = _
  rw [NumberKey.normalize_equal]

@[simp] theorem get_set_self (m : NumberMap υ) (key : Float.Model) (value : υ) :
    get (set m key value) key = some value := by simp

@[simp] theorem get_delete (m : NumberMap υ) (key query : Float.Model) :
    get (delete m key) query =
      if NumberKey.equal key query then none else get m query :=
  @JSMap.get_delete _ _ NumberKey.equality NumberKey.equiv m key query

theorem set_idempotent (m : NumberMap υ) (key : Float.Model) (value : υ) :
    set (set m key value) key value = set m key value :=
  @JSMap.set_idempotent_eq _ _ NumberKey.equality NumberKey.equiv m (NumberKey.normalize key) value

def Normalized (m : NumberMap υ) : Prop :=
  ∀ key ∈ keys m, NumberKey.normalize key = key

theorem normalized_empty : Normalized (empty : NumberMap υ) := by
  simp [Normalized, keys, empty, JSMap.keys, JSMap.empty]

theorem normalized_set (m : NumberMap υ) (key : Float.Model) (value : υ)
    (h : Normalized m) : Normalized (set m key value) := by
  intro query member
  rcases @MapEntries.key_mem_set _ _ NumberKey.equality (@JSMap.entries _ _ NumberKey.equality m)
    (NumberKey.normalize key) value query member with rfl | old
  · exact NumberKey.normalize_idempotent key
  · exact h query old

theorem negative_zero_entries (value : υ) :
    entries (set empty (-(Float.Model.ofNat 0)) value) = [(Float.Model.ofNat 0, value)] := rfl

theorem nan_roundtrip (value : υ) : get (set empty Float.Model.nan value) Float.Model.nan = some value := by
  simp

end NumberMap

namespace NumberSet

def empty : NumberSet := @JSSet.empty _ NumberKey.equality
def has (s : NumberSet) (key : Float.Model) : Bool := @JSSet.has _ NumberKey.equality s key
def add (s : NumberSet) (key : Float.Model) : NumberSet :=
  @JSSet.add _ NumberKey.equality s (NumberKey.normalize key)
def delete (s : NumberSet) (key : Float.Model) : NumberSet := @JSSet.delete _ NumberKey.equality s key
def values (s : NumberSet) : List Float.Model := @JSSet.values _ NumberKey.equality s
def entries (s : NumberSet) : List (Float.Model × Float.Model) := @JSSet.entries _ NumberKey.equality s
def size (s : NumberSet) : Nat := @JSSet.size _ NumberKey.equality s

@[simp] theorem has_empty (key : Float.Model) : has empty key = false := rfl

@[simp] theorem has_add (s : NumberSet) (key query : Float.Model) :
    has (add s key) query = (NumberKey.equal key query || has s query) := by
  rw [has, add, @JSSet.has_add _ NumberKey.equality NumberKey.equiv]
  change (NumberKey.equal (NumberKey.normalize key) query || has s query) = _
  rw [NumberKey.normalize_equal]

@[simp] theorem has_add_self (s : NumberSet) (key : Float.Model) : has (add s key) key = true := by simp

theorem add_idempotent (s : NumberSet) (key : Float.Model) : add (add s key) key = add s key :=
  @JSSet.add_idempotent _ NumberKey.equality NumberKey.equiv s (NumberKey.normalize key)

theorem negative_zero_values : values (add empty (-(Float.Model.ofNat 0))) = [Float.Model.ofNat 0] := rfl

theorem nan_membership : has (add empty Float.Model.nan) Float.Model.nan = true := by simp

end NumberSet
end Ariadne.Shallow

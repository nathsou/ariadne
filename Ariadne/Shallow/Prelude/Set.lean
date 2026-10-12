import Ariadne.Shallow.Prelude.Map

namespace Ariadne.Shallow

/-- A Set has Map's key equivalence, insertion order and uniqueness invariant. -/
structure JSSet (κ : Type) [BEq κ] where
  private map : JSMap κ Unit

namespace JSSet

def empty [BEq κ] : JSSet κ := ⟨JSMap.empty⟩
def has [BEq κ] (s : JSSet κ) (key : κ) : Bool := s.map.has key
def add [BEq κ] (s : JSSet κ) (key : κ) : JSSet κ := ⟨s.map.set key ()⟩
def delete [BEq κ] (s : JSSet κ) (key : κ) : JSSet κ := ⟨s.map.delete key⟩
def values [BEq κ] (s : JSSet κ) : List κ := s.map.keys
def entries [BEq κ] (s : JSSet κ) : List (κ × κ) := s.values.map fun key => (key, key)
def size [BEq κ] (s : JSSet κ) : Nat := s.map.size

def LookupEq [BEq κ] (a b : JSSet κ) : Prop := ∀ key, a.has key = b.has key

@[simp] theorem has_empty [BEq κ] (key : κ) : (empty : JSSet κ).has key = false := rfl
@[simp] theorem has_add [BEq κ] [EquivBEq κ] (s : JSSet κ) (key query : κ) :
    (s.add key).has query = ((key == query) || s.has query) := by
  simp only [has, add, JSMap.has, JSMap.get_set]
  split <;> simp_all
@[simp] theorem has_add_self [BEq κ] [EquivBEq κ] (s : JSSet κ) (key : κ) :
    (s.add key).has key = true := by simp
@[simp] theorem has_delete [BEq κ] [EquivBEq κ] (s : JSSet κ) (key query : κ) :
    (s.delete key).has query = (!(key == query) && s.has query) := by
  simp only [has, delete, JSMap.has, JSMap.get_delete]
  split <;> simp_all

theorem add_idempotent [BEq κ] [EquivBEq κ] (s : JSSet κ) (key : κ) :
    (s.add key).add key = s.add key := by
  simp only [add, JSMap.set_idempotent_eq]

theorem add_comm [BEq κ] [EquivBEq κ] (s : JSSet κ) (a b : κ) :
    LookupEq ((s.add a).add b) ((s.add b).add a) := by
  intro query
  simp only [has_add]
  cases a == query <;> cases b == query <;> rfl

theorem values_add [BEq κ] (s : JSSet κ) (key : κ) :
    (s.add key).values = if s.has key then s.values else s.values ++ [key] :=
  JSMap.keys_set _ _ _

theorem size_add [BEq κ] (s : JSSet κ) (key : κ) :
    (s.add key).size = if s.has key then s.size else s.size + 1 :=
  JSMap.size_set _ _ _

end JSSet
end Ariadne.Shallow

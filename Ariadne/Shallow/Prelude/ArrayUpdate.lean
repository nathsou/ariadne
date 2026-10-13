import Ariadne.Shallow.Prelude.Int53Exact
import Ariadne.Shallow.Prelude.Array
import Ariadne.Shallow.Prelude.NumberKey

namespace Ariadne.Shallow.JSArray

private theorem beq_congr_right (x a b : Float.Model) (same : (a == b) = true) :
    (x == a) = (x == b) := by
  change (a.unpack.compare b.unpack == Option.some .eq) = true at same
  change (x.unpack.compare a.unpack == Option.some .eq) = (x.unpack.compare b.unpack == Option.some .eq)
  rcases ha : a.unpack with ⟨(_ | _)⟩ | _ | ⟨(_ | _)⟩ | ⟨(_ | _), ma, ea, pa⟩ <;>
    rcases hb : b.unpack with ⟨(_ | _)⟩ | _ | ⟨(_ | _)⟩ | ⟨(_ | _), mb, eb, pb⟩
  all_goals simp_all [Float.Model.UnpackedFloat.compare]
  all_goals rcases hx : x.unpack with ⟨(_ | _)⟩ | _ | ⟨(_ | _)⟩ | ⟨(_ | _), mx, ex, px⟩
  all_goals simp_all

/-- A successful dense-array index coercion preserves numeric equality. -/
theorem index_number_eq {query : Float.Model} {index : Nat}
    (valid : Ariadne.indexOf (.number query) = Option.some index) :
    (Float.Model.ofNat index == query) = true := by
  simp only [Ariadne.indexOf] at valid
  split at valid
  · rename_i accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    have equal : (query.unpack.toInt 0 0).toNat = index := Option.some.inj valid
    have integer : (index : Int) = query.unpack.toInt 0 0 := by omega
    change (Float.Model.ofInt (index : Int) == query) = true
    rw [integer]
    exact accepted.2
  · contradiction

/-- Passing numeric inequality separates the actual dense-array indices,
including the two representations of zero. -/
theorem index_guard_distinct {left right : Float.Model} {i j : Nat}
    (leftIndex : Ariadne.indexOf (.number left) = Option.some i)
    (rightIndex : Ariadne.indexOf (.number right) = Option.some j)
    (passed : (left == right) = false) : i ≠ j := by
  intro same
  subst j
  have leftEqual : NumberKey.equal (Float.Model.ofNat i) left = true := by
    simp [NumberKey.equal, index_number_eq leftIndex]
  have rightEqual : NumberKey.equal (Float.Model.ofNat i) right = true := by
    simp [NumberKey.equal, index_number_eq rightIndex]
  have equal := NumberKey.equal_transitive
    (show NumberKey.equal left (Float.Model.ofNat i) = true from
      (NumberKey.equal_symmetric left _).trans leftEqual) rightEqual
  have finite : left.isFinite = true := by
    simp only [Ariadne.indexOf] at leftIndex
    split at leftIndex
    · rename_i accepted
      simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact accepted.1.1
    · contradiction
  have notNaN : left.isNaN = false := by
    cases value : left.unpack <;>
      simp_all [Float.Model.isFinite, Float.Model.isNaN,
        Float.Model.UnpackedFloat.isFinite, Float.Model.UnpackedFloat.isNaN]
  simp [NumberKey.equal, notNaN, passed] at equal

/-- The indexed replacement emitted for a statement projection equals the array
lens update for every valid source index, including negative zero. -/
theorem map_replace_eq_set (xs : List α) (query : Float.Model) (index : Nat) (updated : α)
    (capacity : xs.length < 2 ^ 32) (valid : Ariadne.indexOf (.number query) = Option.some index)
    (present : index < xs.length) :
    map (fun value position => if position == query then updated else value) xs =
      xs.set index updated := by
  have indexRange : Int53.InRange (index : Int) := by
    unfold Int53.InRange Int53.limit
    omega
  have canonical := index_number_eq valid
  apply List.ext_getElem?
  intro i
  by_cases inside : i < xs.length
  · have iRange : Int53.InRange (i : Int) := by
      unfold Int53.InRange Int53.limit
      omega
    have test : (Float.Model.ofNat i == query) = (i == index) := by
      rw [← beq_congr_right (Float.Model.ofNat i) (Float.Model.ofNat index) query canonical]
      change (Float.Model.ofInt (i : Int) == Float.Model.ofInt (index : Int)) = (i == index)
      rw [Int53.beq_ofInt (i : Int) (index : Int) iRange indexRange]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact Int.ofNat_inj
    by_cases equal : i = index
    · subst i
      simp only [map, List.getElem?_mapIdx, test, beq_self_eq_true, ite_true,
        List.getElem?_eq_getElem inside, Option.map_some, List.getElem?_set_self inside]
    · simp [map, List.getElem?_mapIdx, test, List.getElem?_set_ne (Ne.symm equal),
        equal]
  · simp [map, inside]
end Ariadne.Shallow.JSArray

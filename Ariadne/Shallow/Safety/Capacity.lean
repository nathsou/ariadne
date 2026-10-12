import Ariadne.Shallow.Safety.Erasure.Term

namespace Ariadne.Shallow.Safety
open Core

theorem append_capacity {interp : Named.Interp} (left right : List (Model t interp)) :
    binarySafe .append left right = true ↔ (left ++ right).length < 2 ^ 32 := by
  simp [binarySafe, List.length_append]

/-- Array-producing append guards enforce the source array bound. Synthetic
counted-loop ranges do not allocate arrays and have no such capacity guard. -/
theorem append_native_capacity {interp : Named.Interp} (left right : Term Γ (.list t))
    (data : Γ.all dataType = true) (native : Core.Env Γ interp)
    (safe : (term (.binary .append left right) (liftEnvironment Γ data native)).2 = true) :
    (Denote.term (.binary .append left right) native).length < 2 ^ 32 := by
  have guards : ((term left (liftEnvironment Γ data native)).2 = true ∧
      (term right (liftEnvironment Γ data native)).2 = true) ∧
      binarySafe .append (term left (liftEnvironment Γ data native)).1
        (term right (liftEnvironment Γ data native)).1 = true := by
    simpa only [term, Bool.and_eq_true] using safe
  have capacity := (append_capacity _ _).mp guards.2
  have values := term_erases (.binary .append left right) _ native (ErasesEnvironment.lift Γ data native)
  simpa only [← values.length, term, binary] using capacity

theorem cons_native_capacity {interp : Named.Interp} (head : Term Γ t) (tail : Term Γ (.list t))
    (data : Γ.all dataType = true) (native : Core.Env Γ interp)
    (safe : (term (.cons head tail) (liftEnvironment Γ data native)).2 = true) :
    (Denote.term (.cons head tail) native).length < 2 ^ 32 := by
  have guards : ((term head (liftEnvironment Γ data native)).2 = true ∧
      (term tail (liftEnvironment Γ data native)).2 = true) ∧
      decide ((term tail (liftEnvironment Γ data native)).1.length + 1 < 4294967296) = true := by
    simpa only [term, Bool.and_eq_true] using safe
  have capacity : (term tail (liftEnvironment Γ data native)).1.length + 1 < 4294967296 :=
    of_decide_eq_true guards.2
  have values := term_erases (.cons head tail) _ native (ErasesEnvironment.lift Γ data native)
  rw [← values.length]
  simpa [term] using capacity

end Ariadne.Shallow.Safety

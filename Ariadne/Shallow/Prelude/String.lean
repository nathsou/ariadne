import Ariadne.Value
import Init.Data.Order.PackageFactories
import Init.Data.Order.LemmasExtra
namespace Ariadne.Shallow
namespace JSString
/-- Splitting at a delimiter is unambiguous when the first components exclude it. -/
theorem composite_injective (sep : UInt16) (a b c d : Ariadne.JSString)
    (ha : sep ∉ a) (hc : sep ∉ c)
    (same : a ++ [sep] ++ b = c ++ [sep] ++ d) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simpa using same
    | cons x xs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      have : sep ∈ x :: xs := by simp [same.1]
      exact False.elim (hc this)
  | cons x xs ih =>
    cases c with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      have : sep ∈ x :: xs := by simp [same.1]
      exact False.elim (ha this)
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at same
      have result := ih ys (fun h => ha (List.mem_cons_of_mem x h)) (fun h => hc (List.mem_cons_of_mem y h)) same.2
      exact ⟨by simp [same.1, result.1], result.2⟩
end JSString
end Ariadne.Shallow

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
private structure Lex where
  text : Ariadne.JSString
private instance : Ord Lex := ⟨compareOn Lex.text⟩
private instance : Std.TransOrd Lex := inferInstanceAs (Std.TransCmp (compareOn Lex.text))
private instance : Std.LawfulEqOrd Lex where
  eq_of_compare {a b} h := by
    have eq : a.text = b.text := Std.LawfulEqOrd.eq_of_compare h
    cases a; cases b; simp_all
private instance : Std.LinearOrderPackage Lex := .ofOrd Lex

def lt (a b : Ariadne.JSString) : Prop := compare a b = .lt

theorem lt_irrefl (a : Ariadne.JSString) : ¬lt a a := by
  change ¬compare (Lex.mk a) (Lex.mk a) = .lt
  simp

theorem lt_trans {a b c : Ariadne.JSString} (ab : lt a b) (bc : lt b c) : lt a c := by
  have ab : Lex.mk a < Lex.mk b := Std.compare_eq_lt.mp ab
  have bc : Lex.mk b < Lex.mk c := Std.compare_eq_lt.mp bc
  exact (Std.compare_eq_lt (α := Lex)).mpr (Std.lt_trans ab bc)

theorem lt_trichotomy (a b : Ariadne.JSString) : lt a b ∨ a = b ∨ lt b a := by
  rcases Std.lt_trichotomy (Lex.mk a) (Lex.mk b) with h | h | h
  · exact Or.inl ((Std.compare_eq_lt (α := Lex)).mpr h)
  · exact Or.inr (Or.inl (congrArg Lex.text h))
  · exact Or.inr (Or.inr ((Std.compare_eq_lt (α := Lex)).mpr h))

theorem append_assoc (a b c : Ariadne.JSString) : (a ++ b) ++ c = a ++ (b ++ c) := List.append_assoc ..
theorem append_left_cancel (a b c : Ariadne.JSString) (eq : a ++ b = a ++ c) : b = c := List.append_cancel_left eq
theorem append_right_cancel (a b c : Ariadne.JSString) (eq : a ++ c = b ++ c) : a = b := List.append_cancel_right eq
end JSString
end Ariadne.Shallow

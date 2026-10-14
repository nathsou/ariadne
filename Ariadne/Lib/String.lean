import Ariadne.Lib.Sort

/-!
# Strings

`a < b` on strings (`strLt`) compares UTF-16 code units lexicographically: a strict total order. A
comparator that orders strings by it (`a < b ? -1 : b < a ? 1 : 0`) is lawful and tells distinct
strings apart, so `toSorted` with it gives the one strictly ordered arrangement of distinct strings.
-/

namespace Ariadne

theorem strLt_irrefl : ∀ s : JSString, strLt s s = false
  | [] => rfl
  | a :: as => by simp [strLt, strLt_irrefl as]

theorem strLt_asymm : ∀ a b : JSString, strLt a b = true → strLt b a = false
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [strLt] at h
  | x :: xs, y :: ys, h => by
    unfold strLt at h ⊢
    by_cases h1 : x < y
    · have : ¬ y < x := fun h2 => absurd (UInt16.lt_trans h1 h2) (UInt16.lt_irrefl x)
      simp [h1, this]
    · by_cases h2 : y < x
      · simp [h1, h2] at h
      · simp only [h1, h2, ite_false] at h ⊢
        exact strLt_asymm xs ys h

theorem strLt_total : ∀ a b : JSString, a ≠ b → strLt a b = true ∨ strLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => .inl rfl
  | _ :: _, [], _ => .inr rfl
  | x :: xs, y :: ys, h => by
    unfold strLt
    by_cases h1 : x < y
    · simp [h1]
    · by_cases h2 : y < x
      · simp [h2]
      · have hxy : x = y := UInt16.le_antisymm (UInt16.not_lt.mp h2) (UInt16.not_lt.mp h1)
        subst hxy
        have : xs ≠ ys := fun h' => h (by rw [h'])
        simpa [h1] using strLt_total xs ys this

theorem strLt_trans : ∀ a b c : JSString, strLt a b = true → strLt b c = true → strLt a c = true
  | [], [], _, h, _ => by simp [strLt] at h
  | _ :: _, [], _, h, _ => by simp [strLt] at h
  | _, _ :: _, [], _, h => by simp [strLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    unfold strLt at h1 h2 ⊢
    by_cases a1 : x < y
    · by_cases b1 : y < z
      · simp [UInt16.lt_trans a1 b1]
      · by_cases b2 : z < y
        · simp [b1, b2] at h2
        · have hyz : y = z := UInt16.le_antisymm (UInt16.not_lt.mp b2) (UInt16.not_lt.mp b1)
          subst hyz; simp [a1]
    · by_cases a2 : y < x
      · simp [a1, a2] at h1
      · have hxy : x = y := UInt16.le_antisymm (UInt16.not_lt.mp a2) (UInt16.not_lt.mp a1)
        subst hxy
        simp only [a1, ite_false] at h1
        by_cases b1 : x < z
        · simp [b1]
        · by_cases b2 : z < x
          · simp [b1, b2] at h2
          · have hxz : x = z := UInt16.le_antisymm (UInt16.not_lt.mp b2) (UInt16.not_lt.mp b1)
            subst hxz
            simp only [UInt16.lt_irrefl, ite_false] at h2 ⊢
            exact strLt_trans xs ys zs h1 h2

/-- Between distinct strings, not after means before. -/
theorem strLt_of_not {a b : JSString} (h : strLt b a = false) (hne : a ≠ b) : strLt a b = true := by
  rcases strLt_total a b hne with e | e
  · exact e
  · rw [h] at e; cases e

/-- Not before is transitive (the order is total). -/
theorem strLt_false_trans {a b c : JSString} (h1 : strLt a b = false) (h2 : strLt b c = false) :
    strLt a c = false := by
  cases h : strLt a c
  · rfl
  · by_cases hab : a = b
    · subst hab; rw [h2] at h; exact h.symm
    · have hba := strLt_of_not h1 (Ne.symm hab)
      have hca := strLt_trans _ _ _ hba h
      by_cases hbc : b = c
      · subst hbc; rw [strLt_irrefl] at hca; cases hca
      · have := strLt_of_not h2 (Ne.symm hbc)
        rw [strLt_asymm _ _ this] at hca; cases hca

/-- The empty string comes before every other. -/
theorem strLt_nil {a : JSString} (h : a ≠ []) : strLt [] a = true := by
  cases a with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem strLt_nil_right (a : JSString) : strLt a [] = false := by
  cases a <;> rfl

/-- A comparator ordering strings by `<` is lawful, and tells distinct strings apart. -/
theorem strCmp_laws {cmp : JSString → JSString → Int}
    (h : ∀ a b, cmp a b = if strLt a b then -1 else if strLt b a then 1 else 0) :
    CmpLaws cmp ∧ ∀ a b, cmp a b = 0 → a = b := by
  have le : ∀ a b, cmp a b ≤ 0 ↔ strLt b a = false := by
    intro a b; rw [h]
    cases h1 : strLt a b <;> cases h2 : strLt b a <;> simp
    exact absurd (strLt_asymm _ _ h1) (by simp [h2])
  have lt : ∀ a b, cmp a b < 0 ↔ strLt a b = true := by
    intro a b; rw [h]
    cases h1 : strLt a b <;> cases h2 : strLt b a <;> simp
  refine ⟨⟨fun a b => ?_, fun a b c h1 h2 => ?_, fun a b c h1 h2 => ?_, fun a b c h1 h2 => ?_⟩, fun a b h0 => ?_⟩
  · rw [h a b, h b a]
    cases h1 : strLt a b <;> cases h2 : strLt b a <;> simp [sign]
    exact absurd (strLt_asymm _ _ h1) (by simp [h2])
  · rw [le] at *; exact strLt_false_trans h2 h1
  · rw [lt] at h1 ⊢; rw [le] at h2
    by_cases hcb : c = b
    · subst hcb; exact h1
    · exact strLt_trans _ _ _ h1 (strLt_of_not h2 (Ne.symm hcb))
  · rw [lt] at h2 ⊢; rw [le] at h1
    by_cases hab : a = b
    · subst hab; exact h2
    · exact strLt_trans _ _ _ (strLt_of_not h1 hab) h2
  · rw [h] at h0
    cases h1 : strLt a b <;> cases h2 : strLt b a <;> simp_all
    exact Classical.byContradiction fun hne => by rcases strLt_total a b hne with e | e <;> simp_all

end Ariadne

import V2.Typed.Denote

/-!
# Comparators

`toSorted(cmp)` is safe when the comparator is consistent on the array
(`consistent (signs cmp xs)`). A comparator whose signs form a total preorder on all
values (`CmpLaws`) is consistent on every array.
-/

namespace V2

/-- The signs of a comparator form a total preorder. -/
structure CmpLaws {α : Type} (cmp : α → α → Int) : Prop where
  antisymm : ∀ a b, sign (cmp a b) = -sign (cmp b a)
  le_trans : ∀ a b c, cmp a b ≤ 0 → cmp b c ≤ 0 → cmp a c ≤ 0
  lt_of_lt_le : ∀ a b c, cmp a b < 0 → cmp b c ≤ 0 → cmp a c < 0
  lt_of_le_lt : ∀ a b c, cmp a b ≤ 0 → cmp b c < 0 → cmp a c < 0

theorem sign_le_zero {c : Int} : sign c ≤ 0 ↔ c ≤ 0 := by unfold sign; by_cases h1 : c < 0 <;> by_cases h2 : 0 < c <;> simp [h1, h2] <;> omega
theorem sign_lt_zero {c : Int} : sign c < 0 ↔ c < 0 := by unfold sign; by_cases h1 : c < 0 <;> by_cases h2 : 0 < c <;> simp [h1, h2] <;> omega
theorem sign_pos {c : Int} : 0 < sign c ↔ 0 < c := by unfold sign; by_cases h1 : c < 0 <;> by_cases h2 : 0 < c <;> simp [h1, h2] <;> omega

theorem signAt_signs {α : Type} (cmp : α → α → Int) (xs : List α) {i j : Nat} (hi : i < xs.length)
    (hj : j < xs.length) : signAt (signs cmp xs) i j = sign (cmp xs[i] xs[j]) := by
  simp [signAt, signs, hi, hj]

/-- A comparator obeying the laws is consistent on every array. -/
theorem consistent_of_laws {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (xs : List α) :
    consistent (signs cmp xs) = true := by
  have hl : (signs cmp xs).length = xs.length := by simp [signs]
  simp only [consistent, hl, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  intro i hi j hj
  rw [signAt_signs cmp xs hi hj, signAt_signs cmp xs hj hi]
  refine ⟨h.antisymm _ _, fun k hk => ?_⟩
  rw [signAt_signs cmp xs hj hk, signAt_signs cmp xs hi hk]
  have h1 := h.le_trans xs[i] xs[j] xs[k]
  have h2 := h.lt_of_lt_le xs[i] xs[j] xs[k]
  have h3 := h.lt_of_le_lt xs[i] xs[j] xs[k]
  simp only [gt_iff_lt, ge_iff_le] at *
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases a : 0 < sign (cmp xs[i] xs[j])
    · exact .inl (.inl a)
    by_cases b : 0 < sign (cmp xs[j] xs[k])
    · exact .inl (.inr b)
    refine .inr (sign_le_zero.mpr (h1 (sign_le_zero.mp (by omega)) (sign_le_zero.mp (by omega))))
  · by_cases a : 0 ≤ sign (cmp xs[i] xs[j])
    · exact .inl (.inl a)
    by_cases b : 0 < sign (cmp xs[j] xs[k])
    · exact .inl (.inr b)
    refine .inr (sign_lt_zero.mpr (h2 (sign_lt_zero.mp (by omega)) (sign_le_zero.mp (by omega))))
  · by_cases a : 0 < sign (cmp xs[i] xs[j])
    · exact .inl (.inl a)
    by_cases b : 0 ≤ sign (cmp xs[j] xs[k])
    · exact .inl (.inr b)
    refine .inr (sign_lt_zero.mpr (h3 (sign_le_zero.mp (by omega)) (sign_lt_zero.mp (by omega))))

/-! ## Lexicographic comparators -/

/-- Compare integer keys lexicographically (lists of the same length). -/
def lexCmp : List Int → List Int → Int
  | a :: as, b :: bs => if a < b then -1 else if b < a then 1 else lexCmp as bs
  | _, _ => 0

theorem lexCmp_antisymm : ∀ (xs ys : List Int), sign (lexCmp xs ys) = -sign (lexCmp ys xs)
  | a :: as, b :: bs => by
    simp only [lexCmp]
    by_cases h1 : a < b
    · simp [h1, show ¬b < a by omega, sign]
    · by_cases h2 : b < a
      · simp [h1, h2, sign]
      · simp [h1, h2, lexCmp_antisymm as bs]
  | [], [] | [], _ :: _ | _ :: _, [] => by simp [lexCmp, sign]

theorem lexCmp_trans : ∀ (n : Nat) (xs ys zs : List Int), xs.length = n → ys.length = n → zs.length = n →
    (lexCmp xs ys ≤ 0 → lexCmp ys zs ≤ 0 → lexCmp xs zs ≤ 0) ∧
    (lexCmp xs ys < 0 → lexCmp ys zs ≤ 0 → lexCmp xs zs < 0) ∧
    (lexCmp xs ys ≤ 0 → lexCmp ys zs < 0 → lexCmp xs zs < 0)
  | 0, [], [], [], _, _, _ => by simp [lexCmp]
  | n + 1, a :: as, b :: bs, c :: cs, hx, hy, hz => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hx hy hz
    have ih := lexCmp_trans n as bs cs hx hy hz
    simp only [lexCmp]
    by_cases hab : a < b <;> by_cases hba : b < a <;> by_cases hbc : b < c <;> by_cases hcb : c < b <;>
      by_cases hac : a < c <;> by_cases hca : c < a <;> simp [hab, hba, hbc, hcb, hac, hca] <;> omega

/-- Comparing by integer keys of one length, lexicographically, obeys the laws. -/
theorem lexCmp_laws {α : Type} (key : α → List Int) (n : Nat) (hn : ∀ a, (key a).length = n) :
    CmpLaws fun a b => lexCmp (key a) (key b) where
  antisymm _ _ := lexCmp_antisymm _ _
  le_trans a b c := (lexCmp_trans n _ _ _ (hn a) (hn b) (hn c)).1
  lt_of_lt_le a b c := (lexCmp_trans n _ _ _ (hn a) (hn b) (hn c)).2.1
  lt_of_le_lt a b c := (lexCmp_trans n _ _ _ (hn a) (hn b) (hn c)).2.2

theorem CmpLaws.congr {α : Type} {f g : α → α → Int} (h : CmpLaws f) (e : ∀ a b, g a b = f a b) : CmpLaws g where
  antisymm a b := by rw [e, e]; exact h.antisymm a b
  le_trans a b c := by rw [e, e, e]; exact h.le_trans a b c
  lt_of_lt_le a b c := by rw [e, e, e]; exact h.lt_of_lt_le a b c
  lt_of_le_lt a b c := by rw [e, e, e]; exact h.lt_of_le_lt a b c

end V2

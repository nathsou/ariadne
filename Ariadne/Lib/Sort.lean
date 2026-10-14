import Ariadne.Typed.Denote

/-!
# Comparators

`toSorted(cmp)` is safe when the comparator is consistent on the array
(`consistent (signs cmp xs)`). A comparator whose signs form a total preorder on all
values (`CmpLaws`) is consistent on every array.
-/

namespace Ariadne

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


/-! ## What `toSorted` returns

`sortedBy cmp xs` is a permutation of `xs`, ordered by a lawful comparator: each element compares at most
equal to every later one, and strictly less when the comparator tells distinct elements apart. -/

theorem insertBy_perm (s : List (List Int)) (i : Nat) : ∀ js : List Nat, (insertBy s i js).Perm (i :: js)
  | [] => List.Perm.refl _
  | j :: js => by
    unfold insertBy
    split
    · exact List.Perm.refl _
    · exact ((insertBy_perm s i js).cons j).trans (List.Perm.swap i j js)

theorem foldl_insertBy_perm (s : List (List Int)) :
    ∀ (l acc : List Nat), (l.foldl (fun acc i => insertBy s i acc) acc).Perm (l ++ acc)
  | [], acc => List.Perm.refl _
  | i :: l, acc => by
    simp only [List.foldl_cons]
    refine (foldl_insertBy_perm s l _).trans ?_
    refine ((List.Perm.refl l).append (insertBy_perm s i acc)).trans ?_
    simp

theorem sortIndices_perm (s : List (List Int)) (n : Nat) : (sortIndices s n).Perm (List.range n) := by
  simpa [sortIndices] using foldl_insertBy_perm s (List.range n) []

theorem filterMap_range_getElem? {α : Type} : ∀ (xs : List α), (List.range xs.length).filterMap (xs[·]?) = xs
  | [] => rfl
  | x :: xs => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons]
    simp only [List.getElem?_cons_zero, List.filterMap_map]
    congr 1
    simpa [Function.comp_def] using filterMap_range_getElem? xs

/-- `toSorted` returns a permutation of its array. -/
theorem sortedBy_perm {α : Type} (cmp : α → α → Int) (xs : List α) : (sortedBy cmp xs).Perm xs := by
  unfold sortedBy
  have := (sortIndices_perm (signs cmp xs) xs.length).filterMap (xs[·]?)
  rwa [filterMap_range_getElem?] at this

theorem insertBy_sorted {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (xs : List α) (i : Nat)
    (hi : i < xs.length) : ∀ js : List Nat, (∀ j ∈ js, j < xs.length) →
      js.Pairwise (fun a b => ∃ ha hb, cmp (xs[a]'ha) (xs[b]'hb) ≤ 0) →
      (insertBy (signs cmp xs) i js).Pairwise (fun a b => ∃ ha hb, cmp (xs[a]'ha) (xs[b]'hb) ≤ 0)
  | [], _, _ => List.pairwise_singleton _ _
  | j :: js, hb, hp => by
    have hj : j < xs.length := hb j (by simp)
    rw [List.pairwise_cons] at hp
    unfold insertBy
    rw [signAt_signs cmp xs hi hj]
    split
    · rename_i hlt
      have hij : cmp xs[i] xs[j] ≤ 0 := Int.le_of_lt (sign_lt_zero.mp hlt)
      refine List.Pairwise.cons (fun k hk => ?_) (List.Pairwise.cons hp.1 hp.2)
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact ⟨hi, hj, hij⟩
      · obtain ⟨_, hk', hjk⟩ := hp.1 k hk
        exact ⟨hi, hk', h.le_trans _ _ _ hij hjk⟩
    · rename_i hge
      have hji : cmp xs[j] xs[i] ≤ 0 := by
        have := h.antisymm xs[j] xs[i]
        rw [← sign_le_zero, this]
        omega
      refine List.Pairwise.cons (fun k hk => ?_) (insertBy_sorted h xs i hi js (fun k hk => hb k (by simp [hk])) hp.2)
      rcases (List.mem_cons.mp ((insertBy_perm _ i js).mem_iff.mp hk)) with rfl | hk
      · exact ⟨hj, hi, hji⟩
      · exact hp.1 k hk

theorem foldl_insertBy_sorted {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (xs : List α) :
    ∀ (l acc : List Nat), (∀ j ∈ l ++ acc, j < xs.length) →
      acc.Pairwise (fun a b => ∃ ha hb, cmp (xs[a]'ha) (xs[b]'hb) ≤ 0) →
      (l.foldl (fun acc i => insertBy (signs cmp xs) i acc) acc).Pairwise
        (fun a b => ∃ ha hb, cmp (xs[a]'ha) (xs[b]'hb) ≤ 0)
  | [], _, _, hp => hp
  | i :: l, acc, hb, hp => by
    simp only [List.foldl_cons]
    refine foldl_insertBy_sorted h xs l _ (fun j hj => ?_) (insertBy_sorted h xs i (hb i (by simp)) acc
      (fun j hj => hb j (by simp [hj])) hp)
    rcases List.mem_append.mp hj with hj | hj
    · exact hb j (by simp [hj])
    · rcases List.mem_cons.mp ((insertBy_perm _ i acc).mem_iff.mp hj) with rfl | hj
      · exact hb _ (by simp)
      · exact hb j (by simp [hj])

/-- `toSorted` by a lawful comparator returns its array ordered: each element compares at most equal to
every later one. -/
theorem sortedBy_sorted {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (xs : List α) :
    (sortedBy cmp xs).Pairwise (fun a b => cmp a b ≤ 0) := by
  have hp := foldl_insertBy_sorted h xs (List.range xs.length) [] (by simp) List.Pairwise.nil
  unfold sortedBy sortIndices
  have hb : ∀ j ∈ (List.range xs.length).foldl (fun acc i => insertBy (signs cmp xs) i acc) [],
      j < xs.length := fun j hj => by
    have := (foldl_insertBy_perm (signs cmp xs) (List.range xs.length) []).mem_iff.mp hj
    simpa using this
  generalize (List.range xs.length).foldl (fun acc i => insertBy (signs cmp xs) i acc) [] = l at hp hb
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hp
    have ha := hb a (by simp)
    rw [List.filterMap_cons, List.getElem?_eq_getElem ha]
    refine List.Pairwise.cons (fun y hy => ?_) (ih hp.2 (fun j hj => hb j (by simp [hj])))
    obtain ⟨k, hk, hky⟩ := List.mem_filterMap.mp hy
    have hk' := hb k (by simp [hk])
    rw [List.getElem?_eq_getElem hk', Option.some.injEq] at hky
    subst hky
    obtain ⟨_, _, hle⟩ := hp.1 k hk
    exact hle

/-- When the comparator tells distinct elements apart, `toSorted` of an array without repeats is
strictly ordered. -/
theorem sortedBy_strict {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (hz : ∀ a b, cmp a b = 0 → a = b)
    {xs : List α} (hnd : xs.Nodup) : (sortedBy cmp xs).Pairwise (fun a b => cmp a b < 0) := by
  have hnd' : (sortedBy cmp xs).Nodup := (sortedBy_perm cmp xs).nodup_iff.mpr hnd
  refine ((sortedBy_sorted h xs).and hnd').imp fun ⟨hle, hne⟩ => ?_
  rcases Int.lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (hz _ _ heq) hne

/-- Two lists ordered by an antisymmetric relation that hold the same elements are the same list. -/
theorem eq_of_perm_of_pairwise {α : Type} {r : α → α → Prop} (anti : ∀ a b, r a b → r b a → a = b) :
    ∀ {l1 l2 : List α}, l1.Perm l2 → l1.Pairwise r → l2.Pairwise r → l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by have := h.length_eq; simp at this
  | _ :: _, [], h, _, _ => by have := h.length_eq; simp at this
  | a :: t1, b :: t2, h, h1, h2 => by
    have hab : a = b := by
      have ha : a ∈ b :: t2 := h.subset (List.mem_cons_self ..)
      have hb : b ∈ a :: t1 := h.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with e | ha'
      · exact e
      rcases List.mem_cons.mp hb with e | hb'
      · exact e.symm
      exact anti a b (List.rel_of_pairwise_cons h1 hb') (List.rel_of_pairwise_cons h2 ha')
    subst hab
    rw [eq_of_perm_of_pairwise anti ((List.perm_cons a).mp h) h1.of_cons h2.of_cons]

/-- When the comparator tells distinct elements apart, `toSorted` of an array without repeats only
depends on which elements it holds. -/
theorem sortedBy_congr {α : Type} {cmp : α → α → Int} (h : CmpLaws cmp) (hz : ∀ a b, cmp a b = 0 → a = b)
    {xs ys : List α} (hp : xs.Perm ys) (hnd : xs.Nodup) : sortedBy cmp xs = sortedBy cmp ys := by
  refine eq_of_perm_of_pairwise (r := fun a b => cmp a b < 0) (fun a b h1 h2 => ?_)
    ((sortedBy_perm cmp xs).trans (hp.trans (sortedBy_perm cmp ys).symm))
    (sortedBy_strict h hz hnd) (sortedBy_strict h hz (hp.nodup_iff.mp hnd))
  have := h.antisymm a b
  rw [show sign (cmp a b) = -1 from by unfold sign; simp [h1], show sign (cmp b a) = -1 from by unfold sign; simp [h2]]
    at this
  omega

end Ariadne

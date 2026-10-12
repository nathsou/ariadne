import Init.Data.List.Sort.Lemmas
namespace Ariadne.Shallow
namespace StableSort
/-- The comparison is a total preorder: ties need not mean equal values. -/
structure Consistent (le : α → α → Bool) : Prop where
  transitive : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b || le b a

abbrev mergeSort (le : α → α → Bool) (xs : List α) : List α := xs.mergeSort le

theorem permutation (le : α → α → Bool) (xs : List α) : (mergeSort le xs).Perm xs :=
  List.mergeSort_perm xs le

theorem sorted (le : α → α → Bool) (consistent : Consistent le) (xs : List α) :
    (mergeSort le xs).Pairwise (fun a b => le a b = true) :=
  List.pairwise_mergeSort consistent.transitive consistent.total xs

/-- Ties are broken by original position without changing the result. -/
theorem stable (le : α → α → Bool) (xs : List α) :
    ((xs.zipIdx).mergeSort (List.zipIdxLE le)).map Prod.fst = mergeSort le xs :=
  List.mergeSort_zipIdx

theorem tied_sublist (le : α → α → Bool) (consistent : Consistent le)
    (xs ties : List α) (sublist : ties.Sublist xs)
    (tied : ties.Pairwise (fun a b => le a b = true ∧ le b a = true)) :
    ties.Sublist (mergeSort le xs) :=
  List.sublist_mergeSort consistent.transitive consistent.total (tied.imp (fun h => h.1)) sublist

/-- Uniqueness requires antisymmetry; stability handles distinct tied values. -/
theorem unique (le : α → α → Bool) (antisymm : ∀ a b, le a b → le b a → a = b)
    (xs ys : List α) (same : xs.Perm ys) (sx : xs.Pairwise (fun a b => le a b = true))
    (sy : ys.Pairwise (fun a b => le a b = true)) : xs = ys :=
  same.eq_of_pairwise (fun a b _ _ => antisymm a b) sx sy
end StableSort
end Ariadne.Shallow

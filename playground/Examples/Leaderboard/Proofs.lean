import Examples.Leaderboard
import Ariadne.Lib.Cmp

/-!
# Proofs about the leaderboard

`toSorted` denotes `Ariadne.sortedBy`, and its safety condition says the comparator is consistent on the
array. `cmp_laws` proves `byScore` lawful once, for every array, and the sorting library then says what the
sort returns: the same players, best first, in an order that does not depend on the input's.
-/

namespace Examples.Leaderboard.Proofs
open Ariadne Examples.Leaderboard

/-- `byScore` is a total preorder (a chain of keys, which `cmp_laws` recognizes). -/
theorem byScore_laws : CmpLaws «byScore» := by
  cmp_laws

/-- So `ranking` is safe on every array: no precondition is left. -/
theorem ranking_safe (players : List «Player») : «ranking».safe players = true :=
  consistent_of_laws byScore_laws players

/-- The ranking holds exactly the players given. -/
theorem ranking_perm (players : List «Player») : («ranking» players).Perm players :=
  sortedBy_perm _ players

/-- Ordered by `byScore`, a player comes before another only with a score at least as high. -/
theorem score_le_of_byScore {a b : «Player»} (h : «byScore» a b ≤ 0) : b.«score» ≤ a.«score» := by
  unfold «byScore» at h
  split at h
  · split at h <;> simp_all <;> omega
  · simp_all

/-- Best first: scores never increase along the ranking. -/
theorem ranking_sorted (players : List «Player») :
    («ranking» players).Pairwise (fun a b => b.«score» ≤ a.«score») :=
  (sortedBy_sorted byScore_laws players).imp score_le_of_byScore

/-- `byScore` tells distinct players apart. -/
theorem eq_of_byScore_zero (a b : «Player») (h : «byScore» a b = 0) : a = b := by
  obtain ⟨n, s, ⟨⟩⟩ := a
  obtain ⟨m, t, ⟨⟩⟩ := b
  unfold «byScore» at h
  split at h
  · split at h <;> simp at h
  · split at h
    · split at h <;> simp at h
    · simp_all [readable]

/-- The ranking does not depend on the order in which the players were given (for distinct players). -/
theorem ranking_order_independent (xs ys : List «Player») (hp : xs.Perm ys) (hnd : xs.Nodup) :
    «ranking» xs = «ranking» ys :=
  sortedBy_congr byScore_laws eq_of_byScore_zero hp hnd

/-- `best` is the highest score. -/
theorem best_max (players : List «Player») (s : Int) (h : «best» players = some s) :
    ∀ p ∈ players, p.«score» ≤ s := by
  intro p hp
  simp only [«best», listIndex, Int.le_refl, ite_true, Int.toNat_zero] at h
  have hs := ranking_sorted players
  have hm : p ∈ «ranking» players := (ranking_perm players).symm.subset hp
  revert hs hm h
  generalize «ranking» players = r
  rcases r with _ | ⟨top, rest⟩
  · simp
  · intro h hs hm
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Int.le_refl _
    · exact List.rel_of_pairwise_cons hs hm

/-- There is a best score exactly when there are players. -/
theorem best_isSome (players : List «Player») : («best» players).isSome ↔ players ≠ [] := by
  have hl := (ranking_perm players).length_eq
  simp only [«best», listIndex, Int.le_refl, ite_true, Int.toNat_zero]
  revert hl
  generalize «ranking» players = r
  rcases r with _ | ⟨top, rest⟩ <;> rcases players with _ | ⟨p, ps⟩ <;> simp

/-- `qualified` names exactly the players reaching the threshold. -/
theorem mem_qualified (players : List «Player») (threshold : Int) (n : JSString) :
    n ∈ «qualified» players threshold ↔ ∃ p ∈ players, threshold ≤ p.«score» ∧ p.«name» = n := by
  simp only [«qualified», List.mem_map, List.mem_filter, decide_eq_true_eq, ge_iff_le]
  constructor
  · rintro ⟨p, ⟨hp, ht⟩, rfl⟩
    exact ⟨p, (ranking_perm players).subset hp, ht, rfl⟩
  · rintro ⟨p, hp, ht, rfl⟩
    exact ⟨p, ⟨(ranking_perm players).symm.subset hp, ht⟩, rfl⟩

/-- **The claim about the JavaScript.** Every run of `ranking` on an array of players converges to
an array representing the sorted list: no hypothesis on the players is needed. -/
theorem ranking_run (players : List «Player») (vs : List JSValue)
    (args : ArgsRep sig.«ranking».params vs (players, ())) :
    ∃ w, Converges (fun fuel => run ast fuel "ranking" vs) (.ok w) ∧
      Ty.Rep (.array ty.«Player») w («ranking» players) :=
  «ranking».source players vs args (ranking_safe players)

end Examples.Leaderboard.Proofs

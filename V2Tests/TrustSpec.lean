import V2Tests.Generated.Trust
import V2.Lib.Sort

/-!
# drive's trust kernel: specification statements on the v2 translation

The statements of drive's `verify/Drive/Spec/Trust.lean`, restated over the readable
definitions v2 generates from `core/kernel/trust.ts` (unions are sums of their
variants' field tuples, strings are UTF-16 code units), proved there, and carried
over to every JavaScript run by the source theorems.
-/

namespace V2Tests.TrustSpec
open V2 V2Tests.Generated.Trust

/-- Unlock methods may only change from a copy at least as new as what the device saw. -/
theorem may_change_from (written floorWritten : Int) :
    «mayChangeFrom» written floorWritten = true ↔ floorWritten ≤ written := by
  simp [«mayChangeFrom»]

/-- A rotation refuses exactly when a copy holds a seed the session doesn't know. -/
theorem rotated_past (copySeeds ownSeeds : List JSString) :
    «rotatedPast» copySeeds ownSeeds = true ↔ ∃ s ∈ copySeeds, s ∉ ownSeeds := by
  simp only [«rotatedPast», List.any_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  exact exists_congr fun s => and_congr_right fun _ => ⟨fun h hs => h s hs rfl, fun h y hy he => h (he ▸ hy)⟩

/-- A provider's copy, as the sum v2 denotes `StoredCopy` by. -/
abbrev StoredCopy := ty.«StoredCopy».denote

/-- The provider couldn't say. -/
def unknown : StoredCopy := .inr (.inl ())

theorem answered_iff (c : StoredCopy) : «answered» c = true ↔ c ≠ unknown := by
  rcases c with _ | _ | _ | _ | _ | _ <;> simp [«answered», unknown]

/-- Whether a repair may overwrite one provider's copy: never when the session is stale
or read-only; a missing copy only when every provider answered; a copy of the
session's generation only when older; an older or damaged copy always; an unknown or
foreign one never. -/
def MayOverwrite (copies : List StoredCopy) (own : Int) (stale readOnly : Bool) : StoredCopy → Prop
  | .inl _ => stale = false ∧ readOnly = false ∧ ∀ c ∈ copies, c ≠ unknown
  | .inr (.inl _) => False
  | .inr (.inr (.inl (w, _))) => stale = false ∧ readOnly = false ∧ w < own
  | .inr (.inr (.inr (.inl _))) | .inr (.inr (.inr (.inr (.inl _)))) => stale = false ∧ readOnly = false
  | .inr (.inr (.inr (.inr (.inr _)))) => False

/-- **Repairs never destroy.** A repair overwrites exactly the copies `MayOverwrite` allows. -/
theorem repairs_exact (copies : List StoredCopy) (own : Int) (stale readOnly : Bool) :
    («repairs» copies own (stale, readOnly, ())).length = copies.length ∧
      ∀ (i : Nat) c, copies[i]? = some c →
        ((«repairs» copies own (stale, readOnly, ()))[i]? = some true ↔ MayOverwrite copies own stale readOnly c) := by
  have hall : copies.all «answered» = true ↔ ∀ c ∈ copies, c ≠ unknown := by
    simp [List.all_eq_true, answered_iff]
  refine ⟨by simp only [«repairs»]; split <;> simp, fun i c hc => ?_⟩
  simp only [«repairs»]
  split
  · rename_i h
    simp only [Bool.or_eq_true] at h
    simp only [List.getElem?_map, hc, Option.map_some, Option.some.injEq, Bool.false_eq_true, false_iff]
    rcases c with _ | _ | _ | _ | _ | _ <;> rcases h with h | h <;> simp [MayOverwrite, h]
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    simp only [List.getElem?_map, hc, Option.map_some, Option.some.injEq]
    rcases c with _ | _ | _ | _ | _ | _ <;> simp [«repairOne», MayOverwrite, h, hall]

/-! ## The ranking is a total preorder -/

/-- The ranking's keys: committed first, then tagged, then most seeds, then newest, then first. -/
def rankKey (c : ty.«Candidate».denote) : List Int :=
  [if c.2.1 then 0 else 1, if c.2.2.1 then 0 else 1, -c.2.2.2.1, -c.2.2.2.2.1, c.1]

theorem byRank_eq (a b : ty.«Candidate».denote) : «byRank» a b = lexCmp (rankKey a) (rankKey b) := by
  obtain ⟨ia, ca, ta, sa, wa, ⟨⟩⟩ := a
  obtain ⟨ib, cb, tb, sb, wb, ⟨⟩⟩ := b
  have hs : ∀ {R : Type} (x y : Int) (r : R) (p q : R),
      (if (x != y) = true then (if decide (x > y) = true then p else q) else r) =
        (if -x < -y then p else if -y < -x then q else r) := by
    intro R x y r p q
    by_cases h1 : x = y
    · simp [h1]
    · by_cases h2 : y < x
      · simp [h1, h2, show -x < -y by omega]
      · simp [h1, h2, show ¬ -x < -y by omega, show -y < -x by omega]
  have hi : ∀ {R : Type} (x y : Int) (r : R) (p q : R),
      (if (x != y) = true then (if decide (x < y) = true then p else q) else r) =
        (if x < y then p else if y < x then q else r) := by
    intro R x y r p q
    by_cases h1 : x = y
    · simp [h1]
    · by_cases h2 : x < y
      · simp [h1, h2]
      · simp [h1, h2, show y < x by omega]
  cases ca <;> cases cb <;> cases ta <;> cases tb <;>
    simp only [«byRank», rankKey, lexCmp, hs, hi] <;> simp

theorem byRank_laws : CmpLaws «byRank» :=
  (lexCmp_laws rankKey 5 fun _ => rfl).congr byRank_eq

/-- `chooseVaultCopy` is safe on every input: its only condition is that the ranking is
consistent on the copies it sorts. -/
theorem chooseVaultCopy_safe (facts : List ty.«CopyFact».denote) (floor : Option ty.«Floor».denote) :
    «chooseVaultCopy».safe facts floor = true := by
  unfold «chooseVaultCopy».safe
  refine forIn_true (fun p next exit st hn _ => ?_) (fun st => ?_) _ _
  · dsimp only
    split
    · exact hn _
    · split
      · exact hn _
      · split
        · exact hn _
        · split
          · exact hn _
          · split
            · exact hn _
            · exact hn _
  · dsimp only
    split
    · simp [consistent_of_laws byRank_laws]
    · rfl

/-- So every run of the compiled `chooseVaultCopy`, on any arguments representing its
inputs, converges to the readable definition's result: no precondition is left. -/
theorem chooseVaultCopy_run (facts : List ty.«CopyFact».denote) (floor : Option ty.«Floor».denote)
    (vs : List JSValue) (args : ArgsRep sig.«chooseVaultCopy».params vs (facts, floor, ())) :
    ∃ w, Converges (fun fuel => run ast fuel "chooseVaultCopy" vs) (.ok w) ∧
      Ty.Rep ty.«Choice» w («chooseVaultCopy» facts floor) :=
  «chooseVaultCopy».source facts floor vs args (chooseVaultCopy_safe facts floor)

end V2Tests.TrustSpec

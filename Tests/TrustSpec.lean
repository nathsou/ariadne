import Tests.Generated.Trust
import Ariadne.Lib.Cmp

/-!
# drive's trust kernel: specification statements on its translation

The statements of drive's `verify/Drive/Spec/Trust.lean`, restated over the readable
definitions Ariadne generates from `core/kernel/trust.ts` (interfaces are structures,
unions are inductives, strings are UTF-16 code units), proved there, and carried
over to every JavaScript run by the source theorems.
-/

namespace Tests.TrustSpec
open Ariadne Tests.Generated.Trust

/-- Unlock methods may only change from a copy at least as new as what the device saw. -/
theorem may_change_from (written floorWritten : Int) :
    mayChangeFrom written floorWritten = true ↔ floorWritten ≤ written := by
  simp [mayChangeFrom]

/-- A rotation refuses exactly when a copy holds a seed the session doesn't know. -/
theorem rotated_past (copySeeds ownSeeds : List JSString) :
    rotatedPast copySeeds ownSeeds = true ↔ ∃ s ∈ copySeeds, s ∉ ownSeeds := by
  simp only [rotatedPast, List.any_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  exact exists_congr fun s => and_congr_right fun _ => ⟨fun h hs => h s hs rfl, fun h y hy he => h (he ▸ hy)⟩

theorem answered_iff (c : StoredCopy) : answered c = true ↔ c ≠ StoredCopy.unknown := by
  rcases c with _ | _ | _ | _ | _ | _ <;> simp [answered]

/-- Whether a repair may overwrite one provider's copy: never when the session is stale
or read-only; a missing copy only when every provider answered; a copy of the
session's generation only when older; an older or damaged copy always; an unknown or
foreign one never. -/
def MayOverwrite (copies : List StoredCopy) (own : Int) (stale readOnly : Bool) : StoredCopy → Prop
  | .missing => stale = false ∧ readOnly = false ∧ ∀ c ∈ copies, c ≠ StoredCopy.unknown
  | .unknown => False
  | .own w => stale = false ∧ readOnly = false ∧ w < own
  | .older | .damaged => stale = false ∧ readOnly = false
  | .foreign => False

/-- **Repairs never destroy.** A repair overwrites exactly the copies `MayOverwrite` allows. -/
theorem repairs_exact (copies : List StoredCopy) (own : Int) (stale readOnly : Bool) :
    (repairs copies own ⟨stale, readOnly⟩).length = copies.length ∧
      ∀ (i : Nat) c, copies[i]? = some c →
        ((repairs copies own ⟨stale, readOnly⟩)[i]? = some true ↔ MayOverwrite copies own stale readOnly c) := by
  have hall : copies.all answered = true ↔ ∀ c ∈ copies, c ≠ StoredCopy.unknown := by
    simp [List.all_eq_true, answered_iff]
  refine ⟨by simp only [repairs]; split <;> simp, fun i c hc => ?_⟩
  simp only [repairs]
  split
  · rename_i h
    simp only [Bool.or_eq_true] at h
    simp only [List.getElem?_map, hc, Option.map_some, Option.some.injEq, Bool.false_eq_true, false_iff]
    rcases c with _ | _ | _ | _ | _ | _ <;> rcases h with h | h <;> simp_all [MayOverwrite, readable]
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    simp only [List.getElem?_map, hc, Option.map_some, Option.some.injEq]
    rcases c with _ | _ | _ | _ | _ | _ <;> simp_all [repairOne, MayOverwrite, readable]

/-! ## The ranking is a total preorder -/

/-- Committed first, then tagged, then most seeds, then newest, then first: a chain of keys. -/
theorem byRank_laws : CmpLaws byRank := by
  cmp_laws

/-- `chooseVaultCopy` is safe on every input: its only condition is that the ranking is
consistent on the copies it sorts. -/
theorem chooseVaultCopy_safe (facts : List CopyFact) (floor : Option Floor) :
    chooseVaultCopy.safe facts floor = true := by
  unfold chooseVaultCopy.safe
  refine forIn_true (fun p next exit st hn _ => ?_) (fun st => ?_) _ _
  · obtain ⟨_, _⟩ := p
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨⟩⟩ := st
    dsimp only
    repeat' split
    all_goals exact hn _
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨⟩⟩ := st
    dsimp only
    split
    · simp [consistent_of_laws byRank_laws]
    · rfl

/-- So every run of the compiled `chooseVaultCopy`, on any arguments representing its
inputs, converges to the readable definition's result: no precondition is left. -/
theorem chooseVaultCopy_run (facts : List CopyFact) (floor : Option Floor)
    (vs : List JSValue) (args : ArgsRepS names isos sig.chooseVaultCopy.params vs (facts, floor, ())) :
    ∃ w, Converges (fun fuel => run ast fuel "chooseVaultCopy" vs) (.ok w) ∧
      Ty.RepS names isos ty.Choice w (chooseVaultCopy facts floor) :=
  chooseVaultCopy.source facts floor vs args (chooseVaultCopy_safe facts floor)

end Tests.TrustSpec

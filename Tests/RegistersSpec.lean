import Tests.Generated.Registers
import Ariadne.Lib.Map
import Ariadne.Lib.String

/-!
# Properties of drive's registers

Statements about the readable definitions Ariadne generates from `core/kernel/registers.ts`
(a class: its state is a structure of its nine maps; a method that changes the state
denotes the state it leaves). By the generated source theorems,
they hold of every run of the compiled methods.

- Replaying an operation changes nothing (`pack`, `mark`, `item` are idempotent),
  which is what lets a log be applied twice.
- Album items converge: two `item` operations on the same item, applied in either
  order, leave the same register (the later stamp wins).
- An operation on one register leaves the others, by the generated frame lemmas
  (`m.keeps.f`: method `m` never writes the map `f`).
-/

namespace Tests.RegistersSpec

open Ariadne Tests.Generated.Registers

abbrev State := Registers

/-! ## The operations, as updates of one map

Each operation either leaves the state alone or replaces one register. -/

def withMarks (r : State) (m : List (JSString × Mark)) : State := { r with marks := m }

def withPacks (r : State) (m : List (JSString × Pack)) : State := { r with packs := m }

def withItems (r : State) (m : List (JSString × AlbumItem)) : State := { r with items := m }

/-- The register of an album item: the latest operation's stamp and presence. -/
def itemOf (r : State) (aid id : JSString) : Option AlbumItem := mapGet r.items (key aid id)

theorem pack_eq (r : State) (id : JSString) (size csize : Int) (stamp : JSString) (t : Int) (hn : Option JSString) :
    pack r id size csize stamp t hn = if described (mapGet r.packs id) stamp t then r
      else withPacks r (mapPut r.packs id ⟨id, size, csize, t, some stamp, hn⟩) := rfl

theorem mark_eq (r : State) (ref p : JSString) (on : Bool) (reason : Option JSString) (stamp : JSString) (t : Int) :
    mark r ref p on reason stamp t =
      if before stamp (match mapGet r.placed (key ref p) with | none => none | some x => x.u) then r
      else if !newer (match mapGet r.marks (key ref p) with | none => none | some x => some x.s) stamp then r
      else withMarks r (mapPut r.marks (key ref p) ⟨ref, p, t, stamp, on, reason⟩) := rfl

theorem item_eq (r : State) (aid id stamp : JSString) (present : Bool) :
    item r aid id stamp present =
      if newer ((itemOf r aid id).map (·.s)) stamp then
        withItems r (mapPut r.items (key aid id) ⟨aid, id, stamp, present⟩)
      else r := by
  unfold item itemOf
  cases mapGet r.items (key aid id) <;> rfl

/-- A register written at `stamp` is not replaced by a write at the same stamp. -/
theorem newer_self (stamp : JSString) : newer (some stamp) stamp = (stamp == js "") := by
  simp [newer, strLt_irrefl]

/-! ## Replaying an operation changes nothing -/

/-- A pack's description: the earliest wins, so describing it again is ignored. -/
theorem pack_idem (r : State) (id : JSString) (size csize : Int) (stamp : JSString) (t : Int)
    (hn : Option JSString) :
    pack (pack r id size csize stamp t hn) id size csize stamp t hn = pack r id size csize stamp t hn := by
  rw [pack_eq r]
  by_cases h : described (mapGet r.packs id) stamp t = true
  · simp only [h, ite_true]; rw [pack_eq, h]; rfl
  · simp only [h, Bool.false_eq_true, ite_false]
    rw [pack_eq]
    have : described (mapGet (withPacks r (mapPut r.packs id ⟨id, size, csize, t, some stamp, hn⟩)).packs id)
        stamp t = true := by
      simp only [withPacks, mapGet_mapPut, ite_true]
      by_cases hs : stamp = js "" <;> simp [described, hs, strLt_irrefl]
    simp [this]

/-- A deletion mark: the latest wins, so the same mark again changes nothing. -/
theorem mark_idem (r : State) (ref p : JSString) (on : Bool) (reason : Option JSString) (stamp : JSString)
    (t : Int) : mark (mark r ref p on reason stamp t) ref p on reason stamp t = mark r ref p on reason stamp t := by
  rw [mark_eq r]
  by_cases hb : before stamp (match mapGet r.placed (key ref p) with | none => none | some x => x.u) = true
  · simp only [hb, ite_true]; rw [mark_eq, hb]; rfl
  · simp only [hb, Bool.false_eq_true, ite_false]
    by_cases hn : newer (match mapGet r.marks (key ref p) with | none => none | some x => some x.s) stamp = true
    · simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [mark_eq]
      simp only [withMarks, mapGet_mapPut, ite_true, newer_self]
      have hb' : before stamp (match mapGet r.placed (key ref p) with | none => none | some x => x.u) = false := by
        simpa using hb
      by_cases hs : stamp = js ""
      · simp [hs, mapPut_mapPut]
      · simp [hb', hs]
    · simp only [hn, Bool.not_false, ite_true]
      rw [mark_eq]; simp [hb, hn]

/-- An album item: the latest add or remove wins, so the same operation again
changes nothing. -/
theorem item_idem (r : State) (aid id stamp : JSString) (present : Bool) :
    item (item r aid id stamp present) aid id stamp present = item r aid id stamp present := by
  rw [item_eq r]
  by_cases hn : newer ((itemOf r aid id).map (·.s)) stamp = true
  · simp only [hn, ite_true]
    rw [item_eq]
    simp only [itemOf, withItems, mapGet_mapPut, ite_true, Option.map_some, newer_self]
    by_cases hs : stamp = js ""
    · simp [hs, mapPut_mapPut]
    · simp [hs]
  · simp only [hn, Bool.false_eq_true, ite_false]
    rw [item_eq]; simp [hn]

/-! ## Album items converge -/

theorem itemOf_item (r : State) (aid id stamp : JSString) (present : Bool) :
    itemOf (item r aid id stamp present) aid id =
      if newer ((itemOf r aid id).map (·.s)) stamp then some ⟨aid, id, stamp, present⟩ else itemOf r aid id := by
  rw [item_eq]
  split
  · simp [itemOf, withItems, mapGet_mapPut]
  · rfl

/-- Two operations on the same album item with distinct, non-empty stamps leave the
same register whichever arrives first: the later stamp's. -/
theorem item_converges (r : State) (aid id s₁ s₂ : JSString) (p₁ p₂ : Bool) (hne : s₁ ≠ s₂)
    (h₁ : s₁ ≠ js "") (h₂ : s₂ ≠ js "") :
    itemOf (item (item r aid id s₁ p₁) aid id s₂ p₂) aid id =
      itemOf (item (item r aid id s₂ p₂) aid id s₁ p₁) aid id := by
  simp only [itemOf_item]
  have h₁' : (s₁ == js "") = false := beq_eq_false_iff_ne.mpr h₁
  have h₂' : (s₂ == js "") = false := beq_eq_false_iff_ne.mpr h₂
  rcases strLt_total s₁ s₂ hne with hl | hl
  · have hg := strLt_asymm _ _ hl
    cases hc : itemOf r aid id with
    | none => simp [newer, h₁', h₂', hl, hg]
    | some c =>
      have t : strLt c.s s₁ = true → strLt c.s s₂ = true := fun h => strLt_trans _ _ _ h hl
      by_cases hc1 : (newer (some c.s) s₁) = true <;> by_cases hc2 : (newer (some c.s) s₂) = true <;>
        simp_all [newer]
  · have hg := strLt_asymm _ _ hl
    cases hc : itemOf r aid id with
    | none => simp [newer, h₁', h₂', hl, hg]
    | some c =>
      have t : strLt c.s s₂ = true → strLt c.s s₁ = true := fun h => strLt_trans _ _ _ h hl
      by_cases hc1 : (newer (some c.s) s₁) = true <;> by_cases hc2 : (newer (some c.s) s₂) = true <;>
        simp_all [newer]

/-! ## Operations leave the other registers -/

/-- Marking a placement changes no pack. -/
theorem packOf_mark (r : State) (ref p : JSString) (on : Bool) (reason : Option JSString) (stamp : JSString) (t : Int)
    (id : JSString) : packOf (mark r ref p on reason stamp t) id = packOf r id := by
  simp only [packOf, mark.keeps.packs]

/-- Placing or unplacing changes no pack. -/
theorem packOf_place (r : State) (ref p : JSString) (placed : Bool) (cls stamp : JSString) (t : Int) (id : JSString) :
    packOf (place r ref p placed cls stamp t) id = packOf r id := by
  simp only [packOf, place.keeps.packs]

/-- Album operations leave which references are placed. -/
theorem isPlaced_album (r : State) (aid stamp : JSString) (t : Int) (name cover : Option JSString) (deleted : Bool)
    (ref : JSString) : isPlaced (album r aid stamp t name cover deleted) ref = isPlaced r ref := by
  simp only [isPlaced, album.keeps.providers]

end Tests.RegistersSpec

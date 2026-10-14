import V2Tests.Generated.Registers

/-!
# Properties of drive's registers

Statements about the readable definitions v2 generates from `core/kernel/registers.ts`
(a class: its state is a tuple of its nine maps, in declaration order; a method that
changes the state denotes the state it leaves). By the generated source theorems,
they hold of every run of the compiled methods.

- Replaying an operation changes nothing (`pack`, `mark`, `item` are idempotent),
  which is what lets a log be applied twice.
- Album items converge: two `item` operations on the same item, applied in either
  order, leave the same register (the later stamp wins).
-/

namespace V2Tests.RegistersSpec

open V2 V2Tests.Generated.Registers

abbrev State := ty.«Registers».denote

/-! ## Strings and maps -/

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

theorem mapGet_mapPut {α : Type} : ∀ (m : List (JSString × α)) (k j : JSString) (v : α),
    mapGet (mapPut m k v) j = if j = k then some v else mapGet m j
  | [], k, j, v => by by_cases h : j = k <;> simp [mapPut, mapGet, List.lookup, h, beq_eq_false_iff_ne.mpr]
  | (k', w) :: rest, k, j, v => by
    by_cases hk : k' = k
    · subst hk
      by_cases hj : j = k'
      · subst hj; simp [mapPut, mapGet]
      · simp [mapPut, mapGet, List.lookup, hj, beq_eq_false_iff_ne.mpr hj]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [mapPut, hk', Bool.false_eq_true, ite_false]
      have ih := mapGet_mapPut rest k j v
      simp only [mapGet] at ih ⊢
      by_cases hj : j = k'
      · subst hj; simp [List.lookup, hk]
      · simp [List.lookup, beq_eq_false_iff_ne.mpr hj, ih]

theorem mapPut_mapPut {α : Type} : ∀ (m : List (JSString × α)) (k : JSString) (v w : α),
    mapPut (mapPut m k v) k w = mapPut m k w
  | [], k, v, w => by simp [mapPut]
  | (k', x) :: rest, k, v, w => by
    by_cases hk : k' = k
    · subst hk; simp [mapPut]
    · have hk' : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      simp [mapPut, hk', mapPut_mapPut rest k v w]

/-! ## The operations, as updates of one map

Each operation either leaves the state alone or replaces one register. -/

def withMarks (r : State) (m : List (JSString × ty.«Mark».denote)) : State := (r.1, r.2.1, m, r.2.2.2)

def withPacks (r : State) (m : List (JSString × ty.«Pack».denote)) : State := (r.1, r.2.1, r.2.2.1, m, r.2.2.2.2)

def withItems (r : State) (m : List (JSString × ty.«AlbumItem».denote)) : State :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1, m,
    r.2.2.2.2.2.2.2.2.2)

/-- The register of an album item: the latest operation's stamp and presence. -/
def itemOf (r : State) (aid id : JSString) : Option ty.«AlbumItem».denote := mapGet r.2.2.2.2.2.2.2.2.1 («key» aid id)

theorem pack_eq (r : State) (id : JSString) (size csize : Int) (stamp : JSString) (t : Int) (hn : Option JSString) :
    «pack» r id size csize stamp t hn = if «described» (mapGet r.2.2.2.1 id) stamp t then r
      else withPacks r (mapPut r.2.2.2.1 id (id, size, csize, t, some stamp, hn, ())) := rfl

theorem mark_eq (r : State) (ref p : JSString) (on : Bool) (reason : Option JSString) (stamp : JSString) (t : Int) :
    «mark» r ref p on reason stamp t =
      if «before» stamp (match mapGet r.1 («key» ref p) with | none => none | some x => x.2.2.2.2.2.1) then r
      else if !«newer» (match mapGet r.2.2.1 («key» ref p) with | none => none | some x => some x.2.2.2.1) stamp then r
      else withMarks r (mapPut r.2.2.1 («key» ref p) (ref, p, t, stamp, on, reason, ())) := rfl

theorem item_eq (r : State) (aid id stamp : JSString) (present : Bool) :
    «item» r aid id stamp present =
      if «newer» ((itemOf r aid id).map (·.2.2.1)) stamp then
        withItems r (mapPut r.2.2.2.2.2.2.2.2.1 («key» aid id) (aid, id, stamp, present, ()))
      else r := by
  unfold «item» itemOf
  cases mapGet r.2.2.2.2.2.2.2.2.1 («key» aid id) <;> rfl

/-- A register written at `stamp` is not replaced by a write at the same stamp. -/
theorem newer_self (stamp : JSString) : «newer» (some stamp) stamp = (stamp == js "") := by
  simp [«newer», strLt_irrefl]

/-! ## Replaying an operation changes nothing -/

/-- A pack's description: the earliest wins, so describing it again is ignored. -/
theorem pack_idem (r : State) (id : JSString) (size csize : Int) (stamp : JSString) (t : Int)
    (hn : Option JSString) :
    «pack» («pack» r id size csize stamp t hn) id size csize stamp t hn = «pack» r id size csize stamp t hn := by
  rw [pack_eq r]
  by_cases h : «described» (mapGet r.2.2.2.1 id) stamp t = true
  · simp only [h, ite_true]; rw [pack_eq, h]; rfl
  · simp only [h, Bool.false_eq_true, ite_false]
    rw [pack_eq]
    have : «described» (mapGet (withPacks r (mapPut r.2.2.2.1 id (id, size, csize, t, some stamp, hn, ()))).2.2.2.1 id)
        stamp t = true := by
      simp only [withPacks, mapGet_mapPut, ite_true]
      by_cases hs : stamp = js "" <;> simp [«described», hs, strLt_irrefl]
    simp [this]

/-- A deletion mark: the latest wins, so the same mark again changes nothing. -/
theorem mark_idem (r : State) (ref p : JSString) (on : Bool) (reason : Option JSString) (stamp : JSString)
    (t : Int) : «mark» («mark» r ref p on reason stamp t) ref p on reason stamp t = «mark» r ref p on reason stamp t := by
  rw [mark_eq r]
  by_cases hb : «before» stamp (match mapGet r.1 («key» ref p) with | none => none | some x => x.2.2.2.2.2.1) = true
  · simp only [hb, ite_true]; rw [mark_eq, hb]; rfl
  · simp only [hb, Bool.false_eq_true, ite_false]
    by_cases hn : «newer» (match mapGet r.2.2.1 («key» ref p) with | none => none | some x => some x.2.2.2.1) stamp = true
    · simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [mark_eq]
      simp only [withMarks, mapGet_mapPut, ite_true, newer_self]
      have hb' : «before» stamp (match mapGet r.1 («key» ref p) with | none => none | some x => x.2.2.2.2.2.1) = false := by
        simpa using hb
      by_cases hs : stamp = js ""
      · simp [hs, mapPut_mapPut]
      · simp [hb', hs]
    · simp only [hn, Bool.not_false, ite_true]
      rw [mark_eq]; simp [hb, hn]

/-- An album item: the latest add or remove wins, so the same operation again
changes nothing. -/
theorem item_idem (r : State) (aid id stamp : JSString) (present : Bool) :
    «item» («item» r aid id stamp present) aid id stamp present = «item» r aid id stamp present := by
  rw [item_eq r]
  by_cases hn : «newer» ((itemOf r aid id).map (·.2.2.1)) stamp = true
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
    itemOf («item» r aid id stamp present) aid id =
      if «newer» ((itemOf r aid id).map (·.2.2.1)) stamp then some (aid, id, stamp, present, ()) else itemOf r aid id := by
  rw [item_eq]
  split
  · simp [itemOf, withItems, mapGet_mapPut]
  · rfl

/-- Two operations on the same album item with distinct, non-empty stamps leave the
same register whichever arrives first: the later stamp's. -/
theorem item_converges (r : State) (aid id s₁ s₂ : JSString) (p₁ p₂ : Bool) (hne : s₁ ≠ s₂)
    (h₁ : s₁ ≠ js "") (h₂ : s₂ ≠ js "") :
    itemOf («item» («item» r aid id s₁ p₁) aid id s₂ p₂) aid id =
      itemOf («item» («item» r aid id s₂ p₂) aid id s₁ p₁) aid id := by
  simp only [itemOf_item]
  have h₁' : (s₁ == js "") = false := beq_eq_false_iff_ne.mpr h₁
  have h₂' : (s₂ == js "") = false := beq_eq_false_iff_ne.mpr h₂
  rcases strLt_total s₁ s₂ hne with hl | hl
  · have hg := strLt_asymm _ _ hl
    cases hc : itemOf r aid id with
    | none => simp [«newer», h₁', h₂', hl, hg]
    | some c =>
      have t : strLt c.2.2.1 s₁ = true → strLt c.2.2.1 s₂ = true := fun h => strLt_trans _ _ _ h hl
      by_cases hc1 : («newer» (some c.2.2.1) s₁) = true <;> by_cases hc2 : («newer» (some c.2.2.1) s₂) = true <;>
        simp_all [«newer»]
  · have hg := strLt_asymm _ _ hl
    cases hc : itemOf r aid id with
    | none => simp [«newer», h₁', h₂', hl, hg]
    | some c =>
      have t : strLt c.2.2.1 s₂ = true → strLt c.2.2.1 s₁ = true := fun h => strLt_trans _ _ _ h hl
      by_cases hc1 : («newer» (some c.2.2.1) s₁) = true <;> by_cases hc2 : («newer» (some c.2.2.1) s₂) = true <;>
        simp_all [«newer»]

end V2Tests.RegistersSpec

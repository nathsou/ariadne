import V2Tests.Generated.Tree
import V2Tests.RegistersSpec

/-!
# Properties of drive's file tree

Statements about the readable definitions v2 generates from `core/kernel/tree.ts`.
Where a node *sits* (its links) is re-derived on every operation; what is
replicated are two registers per node, and they converge whatever the tree does:

- **Positions** (`spots`): the latest move wins, else the earliest creation.
- **Purges** (`purged`): the earliest purge wins.

The re-derivation (`rearrange`, `attach`, `link`, `unlink`, `settle`) never changes
either register (`*_frame`), so the registers' laws are those of the operations
that write them.
-/

namespace V2Tests.TreeSpec

open V2 V2Tests.Generated.Tree
open V2Tests.RegistersSpec (strLt_irrefl strLt_asymm strLt_total strLt_trans mapGet_mapPut mapPut_mapPut)

abbrev State := ty.«Tree».denote

/-- The two replicated registers of a state. -/
def spots (r : State) : List (JSString × ty.«Spot».denote) := r.1
def purged (r : State) : List (JSString × JSString) := r.2.2.2.2.2.1

/-- `r'` has the registers of `r`. -/
def Frame (r r' : State) : Prop := spots r' = spots r ∧ purged r' = purged r

theorem Frame.refl (r : State) : Frame r r := ⟨rfl, rfl⟩

theorem Frame.trans {r₁ r₂ r₃ : State} (h₁ : Frame r₁ r₂) (h₂ : Frame r₂ r₃) : Frame r₁ r₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

/-! ## Loops -/

/-- An invariant of a loop: if each iteration, from a state satisfying `P`, ends in
`Q` provided continuing and leaving do, and leaving from `P` ends in `Q`, then the
loop does. -/
theorem forIn_inv {α σ R : Type} (P : σ → Prop) (Q : R → Prop) {step : α → (σ → R) → (σ → R) → σ → R}
    {exit : σ → R}
    (hstep : ∀ y next ex s, P s → (∀ s', P s' → Q (next s')) → (∀ s', P s' → Q (ex s')) → Q (step y next ex s))
    (hexit : ∀ s, P s → Q (exit s)) : ∀ (items : List α) s, P s → Q (forIn items step exit s)
  | [], s, h => hexit s h
  | y :: ys, s, h => hstep y _ exit s h (fun s' h' => forIn_inv P Q hstep hexit ys s' h') hexit

/-! ## Re-deriving where nodes sit keeps the registers -/

/-- A method keeps both registers: its result has the input's `spots` (`.1`) and
`purged` (`.2.2.2.2.2.1`). Stated on projections, so `simp` composes them. -/
structure Keeps (r r' : State) : Prop where
  spots : r'.1 = r.1
  purged : r'.2.2.2.2.2.1 = r.2.2.2.2.2.1

macro "keeps" : tactic => `(tactic| (constructor <;> simp_all))

theorem setNext_keeps (r : State) (id : JSString) (n : Option JSString) : Keeps r («setNext» r id n) := by
  unfold «setNext»; dsimp only; split <;> keeps

theorem setPrev_keeps (r : State) (id : JSString) (n : Option JSString) : Keeps r («setPrev» r id n) := by
  unfold «setPrev»; dsimp only; split <;> keeps

@[simp] theorem setNext_1 (r : State) (id : JSString) (n : Option JSString) : («setNext» r id n).1 = r.1 :=
  (setNext_keeps r id n).spots
@[simp] theorem setNext_p (r : State) (id : JSString) (n : Option JSString) :
    («setNext» r id n).2.2.2.2.2.1 = r.2.2.2.2.2.1 := (setNext_keeps r id n).purged
@[simp] theorem setPrev_1 (r : State) (id : JSString) (n : Option JSString) : («setPrev» r id n).1 = r.1 :=
  (setPrev_keeps r id n).spots
@[simp] theorem setPrev_p (r : State) (id : JSString) (n : Option JSString) :
    («setPrev» r id n).2.2.2.2.2.1 = r.2.2.2.2.2.1 := (setPrev_keeps r id n).purged

theorem bury_keeps (r : State) (id b : JSString) : Keeps r («bury» r id b) := by
  unfold «bury»; dsimp only; split <;> keeps

@[simp] theorem bury_1 (r : State) (id b : JSString) : («bury» r id b).1 = r.1 := (bury_keeps r id b).spots
@[simp] theorem bury_p (r : State) (id b : JSString) : («bury» r id b).2.2.2.2.2.1 = r.2.2.2.2.2.1 :=
  (bury_keeps r id b).purged

theorem unlink_keeps (r : State) (id : JSString) : Keeps r («unlink» r id) := by
  unfold «unlink»; dsimp only
  split
  · keeps
  · split
    · keeps
    · split
      · keeps
      · split <;> split <;> keeps

@[simp] theorem unlink_1 (r : State) (id : JSString) : («unlink» r id).1 = r.1 := (unlink_keeps r id).spots
@[simp] theorem unlink_p (r : State) (id : JSString) : («unlink» r id).2.2.2.2.2.1 = r.2.2.2.2.2.1 :=
  (unlink_keeps r id).purged

theorem link_keeps (r : State) (id parent : JSString) : Keeps r («link» r id parent) := by
  unfold «link»; dsimp only
  split <;> split <;> keeps

@[simp] theorem link_1 (r : State) (id p : JSString) : («link» r id p).1 = r.1 := (link_keeps r id p).spots
@[simp] theorem link_p (r : State) (id p : JSString) : («link» r id p).2.2.2.2.2.1 = r.2.2.2.2.2.1 :=
  (link_keeps r id p).purged

/-- A leaf of a loop body: continue or leave with a state that keeps the registers,
or end with one. -/
macro "loop_leaf" hn:ident hx:ident h1:ident h2:ident : tactic => `(tactic| first
  | (apply $hn; constructor <;> simp [$h1:ident, $h2:ident])
  | (apply $hx; constructor <;> simp [$h1:ident, $h2:ident])
  | (constructor <;> simp [$h1:ident, $h2:ident]))

theorem settle_keeps (r : State) (start : JSString) (all : Bool) : Keeps r («settle» r start all) := by
  unfold «settle»; dsimp only
  refine forIn_inv (fun s => Keeps r s.2.2.2.1) (Keeps r) ?_ ?_ _ _ (Keeps.mk rfl rfl)
  · intro y next ex s ⟨h1, h2⟩ hn hx
    repeat' split
    all_goals loop_leaf hn hx h1 h2
  · intro s ⟨h1, h2⟩; exact ⟨h1, h2⟩

@[simp] theorem settle_1 (r : State) (st : JSString) (a : Bool) : («settle» r st a).1 = r.1 :=
  (settle_keeps r st a).spots
@[simp] theorem settle_p (r : State) (st : JSString) (a : Bool) :
    («settle» r st a).2.2.2.2.2.1 = r.2.2.2.2.2.1 := (settle_keeps r st a).purged

theorem attach_keeps (r : State) (id : JSString) : Keeps r («attach» r id) := by
  unfold «attach»; dsimp only
  repeat' split
  all_goals (constructor <;> simp)

@[simp] theorem attach_1 (r : State) (id : JSString) : («attach» r id).1 = r.1 := (attach_keeps r id).spots
@[simp] theorem attach_p (r : State) (id : JSString) : («attach» r id).2.2.2.2.2.1 = r.2.2.2.2.2.1 :=
  (attach_keeps r id).purged

/-- Re-deriving where nodes sit after a node wants another place keeps both registers. -/
theorem rearrange_keeps (r : State) (id : JSString) : Keeps r («rearrange» r id) := by
  unfold «rearrange»; dsimp only
  refine forIn_inv (fun s => Keeps r s.2.2.1) (Keeps r) ?_ ?_ _ _ ⟨by simp, by simp⟩
  · intro y next ex s ⟨h1, h2⟩ hn hx
    exact hn _ ⟨by simp [h1], by simp [h2]⟩
  · intro s ⟨h1, h2⟩
    refine forIn_inv (fun s => Keeps r s.2.2.1) (Keeps r) ?_ ?_ _ _ ⟨h1, h2⟩
    · intro y next ex s ⟨h1, h2⟩ hn hx
      exact hn _ ⟨by simp [h1], by simp [h2]⟩
    · intro s ⟨h1, h2⟩; exact ⟨h1, h2⟩

@[simp] theorem rearrange_1 (r : State) (id : JSString) : («rearrange» r id).1 = r.1 := (rearrange_keeps r id).spots
@[simp] theorem rearrange_p (r : State) (id : JSString) :
    («rearrange» r id).2.2.2.2.2.1 = r.2.2.2.2.2.1 := (rearrange_keeps r id).purged

/-! ## The registers -/

/-- Where a node wants to be (its position register). -/
def spotOf (r : State) (id : JSString) : Option ty.«Spot».denote := mapGet r.1 id

/-- The earliest purge of a node (its purge register). -/
def purgeOf (r : State) (id : JSString) : Option JSString := mapGet r.2.2.2.2.2.1 id

/-- A move (`position … true`) updates the position register: the latest stamp wins;
the creation stamp is kept. -/
theorem position_move_spots (r : State) (id p n st : JSString) :
    («position» r id p n st true).1 =
      match mapGet r.1 id with
      | none => r.1
      | some s => if «newer» s.2.2.1 st then mapPut r.1 id (p, n, some st, s.2.2.2.1, ()) else r.1 := by
  unfold «position»; dsimp only
  split <;> rename_i heq
  · simp only [heq]
  · simp only [heq]
    rename_i _ s
    simp only [ite_true]
    cases hn : «newer» s.2.2.1 st <;> simp

/-- A purge updates the purge register: the earliest stamp wins. -/
theorem purge_purged (r : State) (id st : JSString) :
    («purge» r id st).2.2.2.2.2.1 =
      if id = «root» then r.2.2.2.2.2.1
      else if «earlier» (mapGet r.2.2.2.2.2.1 id) st then mapPut r.2.2.2.2.2.1 id st else r.2.2.2.2.2.1 := by
  unfold «purge»; dsimp only
  by_cases h : id = «root»
  · simp [h]
  · simp only [h, beq_iff_eq, ite_false]
    split <;> simp_all

/-- Purges never change where nodes want to be, and moves never change purges. -/
theorem purge_spots (r : State) (id st : JSString) : («purge» r id st).1 = r.1 := by
  unfold «purge»; dsimp only; split
  · rfl
  · split <;> simp

theorem position_purged (r : State) (id p n st : JSString) (mv : Bool) :
    («position» r id p n st mv).2.2.2.2.2.1 = r.2.2.2.2.2.1 := by
  unfold «position»; dsimp only
  split
  · rfl
  · repeat' split
    all_goals simp

theorem newer_none (st : JSString) : «newer» none st = true := rfl
theorem newer_some (s st : JSString) : «newer» (some s) st = (s == js "" || strLt s st) := rfl
theorem earlier_none (st : JSString) : «earlier» none st = true := rfl
theorem earlier_some (s st : JSString) : «earlier» (some s) st = (s == js "" || strLt st s) := rfl

theorem spotOf_move (r : State) (id p n st : JSString) :
    spotOf («position» r id p n st true) id =
      match spotOf r id with
      | none => none
      | some s => if «newer» s.2.2.1 st then some (p, n, some st, s.2.2.2.1, ()) else some s := by
  unfold spotOf; rw [position_move_spots]
  split <;> rename_i h
  · simp [h]
  · simp only [h]; split <;> simp [mapGet_mapPut, h]

/-- **Moves converge.** Two moves of the same node with distinct, non-empty stamps
leave the same position register whichever arrives first: the later move's. -/
theorem moves_converge (r : State) (id p₁ n₁ s₁ p₂ n₂ s₂ : JSString) (hne : s₁ ≠ s₂) (h₁ : s₁ ≠ js "")
    (h₂ : s₂ ≠ js "") :
    spotOf («position» («position» r id p₁ n₁ s₁ true) id p₂ n₂ s₂ true) id =
      spotOf («position» («position» r id p₂ n₂ s₂ true) id p₁ n₁ s₁ true) id := by
  simp only [spotOf_move]
  have h₁' : (s₁ == js "") = false := beq_eq_false_iff_ne.mpr h₁
  have h₂' : (s₂ == js "") = false := beq_eq_false_iff_ne.mpr h₂
  cases hc : spotOf r id with
  | none => rfl
  | some c =>
    obtain ⟨cw, cn, cp, cm, u⟩ := c
    rcases strLt_total s₁ s₂ hne with hl | hl
    · have hg := strLt_asymm _ _ hl
      cases cp with
      | none => simp [newer_none, newer_some, h₁', h₂', hl, hg]
      | some cp =>
        have t : strLt cp s₁ = true → strLt cp s₂ = true := fun h => strLt_trans _ _ _ h hl
        by_cases hc1 : («newer» (some cp) s₁) = true <;> by_cases hc2 : («newer» (some cp) s₂) = true <;>
          simp_all [newer_some]
    · have hg := strLt_asymm _ _ hl
      cases cp with
      | none => simp [newer_none, newer_some, h₁', h₂', hl, hg]
      | some cp =>
        have t : strLt cp s₂ = true → strLt cp s₁ = true := fun h => strLt_trans _ _ _ h hl
        by_cases hc1 : («newer» (some cp) s₁) = true <;> by_cases hc2 : («newer» (some cp) s₂) = true <;>
          simp_all [newer_some]

theorem purgeOf_purge (r : State) (id st : JSString) (hr : id ≠ «root») :
    purgeOf («purge» r id st) id = if «earlier» (purgeOf r id) st then some st else purgeOf r id := by
  unfold purgeOf; rw [purge_purged]
  simp only [hr, ite_false]
  split <;> simp [mapGet_mapPut]

/-- **Purges converge.** Two purges of a node with distinct, non-empty stamps leave
the same purge register whichever arrives first: the earlier stamp. -/
theorem purges_converge (r : State) (id s₁ s₂ : JSString) (hr : id ≠ «root») (hne : s₁ ≠ s₂)
    (h₁ : s₁ ≠ js "") (h₂ : s₂ ≠ js "") :
    purgeOf («purge» («purge» r id s₁) id s₂) id = purgeOf («purge» («purge» r id s₂) id s₁) id := by
  simp only [purgeOf_purge _ _ _ hr]
  have h₁' : (s₁ == js "") = false := beq_eq_false_iff_ne.mpr h₁
  have h₂' : (s₂ == js "") = false := beq_eq_false_iff_ne.mpr h₂
  rcases strLt_total s₁ s₂ hne with hl | hl
  · have hg := strLt_asymm _ _ hl
    cases hc : purgeOf r id with
    | none => simp [earlier_none, earlier_some, h₁', h₂', hl, hg]
    | some c =>
      have t : strLt s₂ c = true → strLt s₁ c = true := fun h => strLt_trans _ _ _ hl h
      by_cases hc1 : («earlier» (some c) s₁) = true <;> by_cases hc2 : («earlier» (some c) s₂) = true <;>
        simp_all [earlier_some]
  · have hg := strLt_asymm _ _ hl
    cases hc : purgeOf r id with
    | none => simp [earlier_none, earlier_some, h₁', h₂', hl, hg]
    | some c =>
      have t : strLt s₁ c = true → strLt s₂ c = true := fun h => strLt_trans _ _ _ hl h
      by_cases hc1 : («earlier» (some c) s₁) = true <;> by_cases hc2 : («earlier» (some c) s₂) = true <;>
        simp_all [earlier_some]

/-- **A move and a purge commute** on the registers: each leaves the other's alone. -/
theorem move_purge_commute (r : State) (id p n sm j sp : JSString) :
    spotOf («purge» («position» r id p n sm true) j sp) id = spotOf («position» («purge» r j sp) id p n sm true) id ∧
      purgeOf («purge» («position» r id p n sm true) j sp) j =
        purgeOf («position» («purge» r j sp) id p n sm true) j := by
  constructor
  · simp only [spotOf, purge_spots, position_move_spots]
  · by_cases hr : j = «root»
    · simp [purgeOf, purge_purged, hr, position_purged]
    · simp [purgeOf, purge_purged, hr, position_purged]

end V2Tests.TreeSpec

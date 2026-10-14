import Tests.Generated.Tree
import Ariadne.Lib.Loop
import Tests.RegistersSpec

/-!
# Properties of drive's file tree

Statements about the readable definitions Ariadne generates from `core/kernel/tree.ts`.
Where a node *sits* (its links) is re-derived on every operation; what is
replicated are two registers per node, and they converge whatever the tree does:

- **Positions** (`spots`): the latest move wins, else the earliest creation.
- **Purges** (`purged`): the earliest purge wins.

The re-derivation (`rearrange`, `attach`, `link`, `unlink`, `settle`) never changes
either register (`*_frame`), so the registers' laws are those of the operations
that write them.

Re-deriving where nodes sit starts from the cycles of wanted parents, found by
`cycleOf`: what it returns is such a cycle through the node (`cycleOf_cycle`), and
it finds every one (`cycleOf_finds_all`): its bound of one step per node is enough,
because a longer walk back to the node repeats a node and so has a shorter one.
-/

namespace Tests.TreeSpec

open Ariadne Tests.Generated.Tree
open Tests.RegistersSpec (strLt_irrefl strLt_asymm strLt_total strLt_trans mapGet_mapPut mapPut_mapPut)

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

/-! ## Cycles of wanted parents -/

/-- Each node of the list wants the next one as its parent. -/
def Chain (sp : List (JSString × ty.«Spot».denote)) : List JSString → Prop
  | x :: y :: rest => (∃ s, mapGet sp x = some s ∧ s.1 = y) ∧ Chain sp (y :: rest)
  | _ => True

theorem chain_snoc (sp : List (JSString × ty.«Spot».denote)) {c : JSString} {s : ty.«Spot».denote}
    (hs : mapGet sp c = some s) : ∀ {path : List JSString}, Chain sp path → path.getLast? = some c →
      Chain sp (path ++ [s.1])
  | [], _, hl => by simp at hl
  | [x], _, hl => by simp at hl; subst hl; exact ⟨⟨s, hs, rfl⟩, trivial⟩
  | x :: y :: rest, ⟨h1, h2⟩, hl => ⟨h1, chain_snoc sp hs (path := y :: rest) h2 (by simpa using hl)⟩

/-- A loop invariant indexed by how many iterations remain, with a separate
condition for leaving early (`break`). -/
theorem forIn_inv_len {α σ R : Type} (P : Nat → σ → Prop) (B : σ → Prop) (Q : R → Prop)
    {step : α → (σ → R) → (σ → R) → σ → R} {exit : σ → R}
    (hstep : ∀ y n next ex s, P (n + 1) s → (∀ s', P n s' → Q (next s')) → (∀ s', B s' → Q (ex s')) →
      Q (step y next ex s))
    (hend : ∀ s, P 0 s → Q (exit s)) (hbrk : ∀ s, B s → Q (exit s)) :
    ∀ (items : List α) s, P items.length s → Q (forIn items step exit s)
  | [], s, h => hend s h
  | y :: ys, s, h => hstep y ys.length _ exit s h (fun s' h' => forIn_inv_len P B Q hstep hend hbrk ys s' h') hbrk

/-- Where `k` steps up the wanted parents from `x` lead (none if a node on the way
has no spot). -/
def up (sp : List (JSString × ty.«Spot».denote)) : Nat → JSString → Option JSString
  | 0, x => some x
  | k + 1, x => (up sp k x).bind fun c => (mapGet sp c).map (·.1)

theorem up_none (sp : List (JSString × ty.«Spot».denote)) (x : JSString) {j : Nat} (h : up sp j x = none) :
    ∀ m, j ≤ m → up sp m x = none := by
  intro m hm
  induction m with
  | zero => cases j <;> simp_all [up]
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact h
    · simp [up, ih (by omega)]

/-- What `cycleOf` returns, when not empty: a cycle of wanted parents through `id`. -/
def Cycle (r : State) (id : JSString) (path : List JSString) : Prop :=
  path = [] ∨ (path.head? = some id ∧ Chain r.1 path ∧
    ∃ c s, path.getLast? = some c ∧ mapGet r.1 c = some s ∧ s.1 = id)

/-- **`cycleOf` returns a cycle**: its result is empty, or starts at `id`, each node
on it wants the next as its parent, and the last wants `id`. -/
theorem cycleOf_cycle (r : State) (id : JSString) : Cycle r id («cycleOf» r id) := by
  unfold «cycleOf»; dsimp only
  have hlen : (Ariadne.range (List.length r.1 : Int)).length = r.1.length := by simp [Ariadne.range]
  refine forIn_inv_len
    (fun n s => s.2.2.2.1 = r ∧ s.2.2.2.2.1 = id ∧ s.1 = false ∧ up r.1 (r.1.length - n) id = some s.2.1 ∧
      n ≤ r.1.length ∧ s.2.2.1 = (r.1.length : Int))
    (fun s => s.2.2.2.1 = r ∧ s.2.2.2.2.1 = id ∧ s.1 = true ∧ s.2.2.1 = (r.1.length : Int) ∧
      ∃ k, 1 ≤ k ∧ k ≤ r.1.length ∧ up r.1 k id = some id)
    (Cycle r id) ?_ ?_ ?_ _ _ ?_
  · intro y n next ex s ⟨h1, h2, h3, h4, h5, h6⟩ hn hx
    split
    · exact Or.inl rfl
    · rename_i sp hsp
      rw [h1] at hsp
      have hup : up r.1 (r.1.length - n) id = some sp.1 := by
        have : r.1.length - n = (r.1.length - (n + 1)) + 1 := by omega
        rw [this]; simp [up, h4, hsp]
      split
      · rename_i heq
        refine hx _ ⟨h1, h2, rfl, h6, r.1.length - n, by omega, by omega, ?_⟩
        rw [hup]; simpa [h2] using heq
      · exact hn _ ⟨h1, h2, h3, hup, by omega, h6⟩
  · intro s ⟨_, _, h3, _, _⟩; simp [h3]; exact Or.inl rfl
  · intro s ⟨h1, h2, h3, h4, k, hk1, hk2, hk⟩
    simp only [h3, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [h4]
    refine forIn_inv_len
      (fun n t => t.2.2.2.2.1 = r ∧ t.2.2.2.2.2.1 = id ∧ t.1.head? = some id ∧ Chain r.1 t.1 ∧
        t.1.getLast? = some t.2.2.1 ∧ ∃ j, j + n = r.1.length ∧ j < k ∧ up r.1 j id = some t.2.2.1)
      (fun _ => False) (Cycle r id) ?_ ?_ (fun _ h => h.elim) _ _ ?_
    · intro y n next ex t ⟨g1, g2, g3, g4, g5, j, hj1, hj2, hj3⟩ hn _
      split
      · rename_i hsp
        rw [g1] at hsp
        have : up r.1 (j + 1) id = none := by simp [up, hj3, hsp]
        rw [up_none r.1 id this k (by omega)] at hk; simp at hk
      · rename_i sp hsp
        rw [g1] at hsp
        have hup : up r.1 (j + 1) id = some sp.1 := by simp [up, hj3, hsp]
        split
        · rename_i heq
          exact Or.inr ⟨g3, g4, _, sp, g5, hsp, by simpa [g2] using heq⟩
        · rename_i hne
          refine hn _ ⟨g1, g2, ?_, ?_, by simp, j + 1, by omega, ?_, hup⟩
          · cases hp : t.1 with
            | nil => simp [hp] at g3
            | cons a l => simp [hp] at g3 ⊢; exact g3
          · exact chain_snoc _ hsp g4 g5
          · rcases Nat.lt_or_ge (j + 1) k with h | h
            · exact h
            · have : j + 1 = k := by omega
              subst this; rw [hup] at hk; simp [g2] at hne; simp at hk; exact absurd hk hne
    · intro t ⟨_, _, _, _, _, j, hj1, hj2, _⟩; omega
    · refine ⟨h1, h2, by simp [h2], trivial, by simp [h2], 0, ?_, by omega, by simp [up, h2]⟩
      simp [Ariadne.range]
  · exact ⟨rfl, rfl, rfl, by simp [hlen, up], by simp [hlen], rfl⟩

/-- **`cycleOf` finds every cycle** through `id` no longer than the number of nodes
with a spot. -/
theorem cycleOf_finds (r : State) (id : JSString) {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ r.1.length)
    (hk : up r.1 k id = some id) : «cycleOf» r id ≠ [] := by
  unfold «cycleOf»; dsimp only
  have hlen : (Ariadne.range (List.length r.1 : Int)).length = r.1.length := by simp [Ariadne.range]
  refine forIn_inv_len
    (fun n s => s.2.2.2.1 = r ∧ s.2.2.2.2.1 = id ∧ up r.1 (r.1.length - n) id = some s.2.1 ∧
      n ≤ r.1.length ∧ r.1.length - n < k)
    (fun s => s.1 = true) (· ≠ []) ?_ ?_ ?_ _ _ ?_
  · intro y n next ex s ⟨h1, h2, h4, h5, h6⟩ hn hx
    split
    · rename_i hsp
      rw [h1] at hsp
      have : up r.1 (r.1.length - n) id = none := by
        have : r.1.length - n = (r.1.length - (n + 1)) + 1 := by omega
        rw [this]; simp [up, h4, hsp]
      rw [up_none r.1 id this k (by omega)] at hk; simp at hk
    · rename_i sp hsp
      rw [h1] at hsp
      have hup : up r.1 (r.1.length - n) id = some sp.1 := by
        have : r.1.length - n = (r.1.length - (n + 1)) + 1 := by omega
        rw [this]; simp [up, h4, hsp]
      split
      · exact hx _ rfl
      · rename_i hne
        refine hn _ ⟨h1, h2, hup, by omega, ?_⟩
        rcases Nat.lt_or_ge (r.1.length - n) k with h | h
        · exact h
        · have : r.1.length - n = k := by omega
          rw [this] at hup; rw [hup] at hk; simp at hk; simp [h2, hk] at hne
  · intro s ⟨_, _, _, _, h6⟩; omega
  · intro s h3
    simp only [h3, Bool.not_true, Bool.false_eq_true, ite_false]
    refine forIn_inv_len (fun _ t => t.1 ≠ []) (fun _ => False) (· ≠ []) ?_ ?_ (fun _ h => h.elim) _ _ (by simp)
    · intro y n next ex t g hn _
      split
      · exact g
      · split
        · exact g
        · exact hn _ (by simp)
    · intro t g; exact g
  · exact ⟨rfl, rfl, by simp [hlen, up], by simp [hlen], by simp [hlen]; omega⟩

/-! ### Every cycle is short enough

A walk up the wanted parents that returns to `id` after more steps than there are
nodes visits some node twice, so a shorter walk returns too: `cycleOf` finds every
cycle through `id`. -/

theorem up_add (sp : List (JSString × ty.«Spot».denote)) (x : JSString) (a : Nat) :
    ∀ m, up sp (a + m) x = (up sp a x).bind (fun y => up sp m y)
  | 0 => by cases up sp a x <;> simp [up]
  | m + 1 => by
    rw [← Nat.add_assoc]; simp only [up]; rw [up_add sp x a m]
    cases up sp a x <;> simp

theorem mem_keys_of_lookup {α : Type} : ∀ {sp : List (JSString × α)} {c : JSString} {v : α},
    sp.lookup c = some v → c ∈ sp.map Prod.fst
  | [], _, _, h => by simp at h
  | (k, w) :: rest, c, v, h => by
    by_cases hc : c = k
    · simp [hc]
    · have : (c == k) = false := beq_eq_false_iff_ne.mpr hc
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_keys_of_lookup h)

theorem nodup_map_range {β : Type} (f : Nat → β) :
    ∀ k, (∀ i j, i < k → j < k → f i = f j → i = j) → ((List.range k).map f).Nodup
  | 0, _ => by simp
  | k + 1, h => by
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨nodup_map_range f k (fun i j hi hj => h i j (by omega) (by omega)), by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    obtain ⟨i, hi, rfl⟩ := ha
    subst hb
    intro he
    have := h i k (by omega) (by omega) he
    omega

/-- A walk that returns to `id` after more steps than there are nodes has a shorter one. -/
theorem up_shorter (r : State) (id : JSString) {k : Nat} (hk : up r.1 k id = some id)
    (hlong : r.1.length < k) : ∃ k', 1 ≤ k' ∧ k' < k ∧ up r.1 k' id = some id := by
  refine Classical.byContradiction fun hno => ?_
  have hinj : ∀ i j, i < k → j < k → up r.1 i id = up r.1 j id → i = j := by
    have key : ∀ i j, i < j → j < k → up r.1 i id = up r.1 j id → False := by
      intro i j hij hj he
      have h1 : up r.1 (i + (k - j)) id = some id := by
        rw [up_add, he, ← up_add, show j + (k - j) = k by omega, hk]
      exact hno ⟨i + (k - j), by omega, by omega, h1⟩
    intro i j hi hj he
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact (key i j h hj he).elim
    · exact h
    · exact (key j i h hi he.symm).elim
  have hnd := nodup_map_range (fun i => up r.1 i id) k hinj
  have hsub : (List.range k).map (fun i => up r.1 i id) ⊆ r.1.map (fun p => some p.1) := by
    intro o ho
    simp only [List.mem_map, List.mem_range] at ho
    obtain ⟨i, hi, rfl⟩ := ho
    cases hc : up r.1 i id with
    | none => rw [up_none r.1 id hc k (by omega)] at hk; simp at hk
    | some c =>
      cases hs : mapGet r.1 c with
      | none =>
        have : up r.1 (i + 1) id = none := by simp [up, hc, hs]
        rw [up_none r.1 id this k (by omega)] at hk; simp at hk
      | some v =>
        have := mem_keys_of_lookup (sp := r.1) hs
        simp only [List.mem_map] at this ⊢
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨p, hp, rfl⟩
  have := hnd.length_le_of_subset hsub
  simp at this
  omega

/-- **`cycleOf` finds every cycle** of wanted parents through `id`. -/
theorem cycleOf_finds_all (r : State) (id : JSString) :
    ∀ k, 1 ≤ k → up r.1 k id = some id → «cycleOf» r id ≠ [] := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk1 hk
    by_cases hle : k ≤ r.1.length
    · exact cycleOf_finds r id hk1 hle hk
    · obtain ⟨k', h1, h2, h3⟩ := up_shorter r id hk (by omega)
      exact ih k' h2 h1 h3

end Tests.TreeSpec

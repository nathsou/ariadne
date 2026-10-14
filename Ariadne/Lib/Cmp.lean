import Ariadne.Lib.Sort
import Ariadne.Lib.String

/-!
# Lawful comparators, by shape

`toSorted(cmp)` is safe when `cmp` obeys `CmpLaws` (`consistent_of_laws`). Comparators are usually
written as a chain of keys: compare one key, and on a tie the next, down to `return 0`. This file
proves the laws for the shapes such chains take in readable definitions, and `cmp_laws` proves them for
a whole chain:

```
theorem byRank_laws : CmpLaws «byRank» := by cmp_laws
```

Recognized links, for a key `k` (a field, or the value itself) of type `Bool`, `Int` or `JSString`:
`if k a != k b then (if <a before b> then -1 else 1) else …` (by `<`, `>`, or for booleans `true`
first or last); `if k a < k b then -1 else if k b < k a then 1 else …` (either direction); and the
ends `0`, `k a - k b` and `k b - k a`.
-/

namespace Ariadne

theorem CmpLaws.zero {α : Type} : CmpLaws (fun (_ _ : α) => (0 : Int)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => Int.le_refl 0, fun _ _ _ h _ => absurd h (Int.lt_irrefl 0),
    fun _ _ _ _ h => absurd h (Int.lt_irrefl 0)⟩

theorem CmpLaws.sub {α : Type} (key : α → Int) : CmpLaws (fun a b => key a - key b) where
  antisymm a b := by
    have : key b - key a = -(key a - key b) := by omega
    rw [this]; unfold sign; split <;> split <;> (try split) <;> (try split) <;> omega
  le_trans _ _ _ h1 h2 := by omega
  lt_of_lt_le _ _ _ h1 h2 := by omega
  lt_of_le_lt _ _ _ h1 h2 := by omega

theorem CmpLaws.subRev {α : Type} (key : α → Int) : CmpLaws (fun a b => key b - key a) :=
  (CmpLaws.sub fun a => -key a).congr fun a b => by omega

/-- Comparing by a key first, in a strict total order `lt`, and on a tie by `rest`. -/
theorem CmpLaws.keyThen {α β : Type} [DecidableEq β] (key : α → β) (lt : β → β → Bool)
    (irrefl : ∀ x, lt x x = false) (trans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true)
    (total : ∀ x y, x ≠ y → lt x y = true ∨ lt y x = true) {rest : α → α → Int} (hr : CmpLaws rest) :
    CmpLaws (fun a b => if key a = key b then rest a b else if lt (key a) (key b) then -1 else 1) := by
  have asymm : ∀ x y, lt x y = true → lt y x = false := fun x y h => by
    cases h' : lt y x
    · rfl
    · have := trans _ _ _ h h'; simp [irrefl] at this
  have le : ∀ a b, (if key a = key b then rest a b else if lt (key a) (key b) then -1 else 1) ≤ 0 ↔
      (key a = key b ∧ rest a b ≤ 0) ∨ (key a ≠ key b ∧ lt (key a) (key b) = true) := by
    intro a b; by_cases e : key a = key b <;> by_cases l : lt (key a) (key b) <;> simp [e, l]
  have lt0 : ∀ a b, (if key a = key b then rest a b else if lt (key a) (key b) then -1 else 1) < 0 ↔
      (key a = key b ∧ rest a b < 0) ∨ (key a ≠ key b ∧ lt (key a) (key b) = true) := by
    intro a b; by_cases e : key a = key b <;> by_cases l : lt (key a) (key b) <;> simp [e, l]
  have chain : ∀ a b c, key a ≠ key b → lt (key a) (key b) = true → key b ≠ key c → lt (key b) (key c) = true →
      key a ≠ key c ∧ lt (key a) (key c) = true := fun a b c _ l1 _ l2 => by
    have l := trans _ _ _ l1 l2
    exact ⟨fun e => by rw [e, irrefl] at l; exact absurd l (by decide), l⟩
  refine ⟨fun a b => ?_, fun a b c h1 h2 => ?_, fun a b c h1 h2 => ?_, fun a b c h1 h2 => ?_⟩
  · by_cases e : key a = key b
    · simp [e, hr.antisymm a b]
    · have e' : key b ≠ key a := Ne.symm e
      rcases total _ _ e with l | l
      · simp [e, e', l, asymm _ _ l, sign]
      · simp [e, e', l, asymm _ _ l, sign]
  · rw [le] at h1 h2 ⊢
    rcases h1 with ⟨e1, r1⟩ | ⟨n1, l1⟩ <;> rcases h2 with ⟨e2, r2⟩ | ⟨n2, l2⟩
    · exact .inl ⟨e1.trans e2, hr.le_trans _ _ _ r1 r2⟩
    · exact .inr ⟨by rw [e1]; exact n2, by rw [e1]; exact l2⟩
    · exact .inr ⟨by rw [← e2]; exact n1, by rw [← e2]; exact l1⟩
    · exact .inr (chain a b c n1 l1 n2 l2)
  · rw [lt0] at h1 ⊢; rw [le] at h2
    rcases h1 with ⟨e1, r1⟩ | ⟨n1, l1⟩ <;> rcases h2 with ⟨e2, r2⟩ | ⟨n2, l2⟩
    · exact .inl ⟨e1.trans e2, hr.lt_of_lt_le _ _ _ r1 r2⟩
    · exact .inr ⟨by rw [e1]; exact n2, by rw [e1]; exact l2⟩
    · exact .inr ⟨by rw [← e2]; exact n1, by rw [← e2]; exact l1⟩
    · exact .inr (chain a b c n1 l1 n2 l2)
  · rw [le] at h1; rw [lt0] at h2 ⊢
    rcases h1 with ⟨e1, r1⟩ | ⟨n1, l1⟩ <;> rcases h2 with ⟨e2, r2⟩ | ⟨n2, l2⟩
    · exact .inl ⟨e1.trans e2, hr.lt_of_le_lt _ _ _ r1 r2⟩
    · exact .inr ⟨by rw [e1]; exact n2, by rw [e1]; exact l2⟩
    · exact .inr ⟨by rw [← e2]; exact n1, by rw [← e2]; exact l1⟩
    · exact .inr (chain a b c n1 l1 n2 l2)

/-- A key chain link with the order's `lt` and its converse spelled as the source does. -/
theorem CmpLaws.threeWay {α β : Type} [DecidableEq β] (key : α → β) (lt : β → β → Bool)
    (irrefl : ∀ x, lt x x = false) (trans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true)
    (total : ∀ x y, x ≠ y → lt x y = true ∨ lt y x = true) {rest : α → α → Int} (hr : CmpLaws rest) :
    CmpLaws (fun a b => if lt (key a) (key b) then -1 else if lt (key b) (key a) then 1 else rest a b) := by
  refine (CmpLaws.keyThen key lt irrefl trans total hr).congr fun a b => ?_
  by_cases e : key a = key b
  · simp [e, irrefl]
  · rcases total _ _ e with l | l
    · simp [e, l]
    · have : lt (key a) (key b) = false := by
        cases h : lt (key a) (key b)
        · rfl
        · have := trans _ _ _ h l; simp [irrefl] at this
      simp [e, l, this]

/-! ## The orders keys take -/

theorem intLt_irrefl (x : Int) : decide (x < x) = false := by simp
theorem intLt_trans (x y z : Int) (h1 : decide (x < y) = true) (h2 : decide (y < z) = true) : decide (x < z) = true := by
  simp at *; omega
theorem intLt_total (x y : Int) (h : x ≠ y) : decide (x < y) = true ∨ decide (y < x) = true := by
  simp; omega

theorem intGt_irrefl (x : Int) : decide (x > x) = false := by simp
theorem intGt_trans (x y z : Int) (h1 : decide (x > y) = true) (h2 : decide (y > z) = true) : decide (x > z) = true := by
  simp at *; omega
theorem intGt_total (x y : Int) (h : x ≠ y) : decide (x > y) = true ∨ decide (y > x) = true := by
  simp; omega

theorem strGt_trans (x y z : JSString) (h1 : strLt y x = true) (h2 : strLt z y = true) : strLt z x = true :=
  strLt_trans _ _ _ h2 h1

theorem strLt_total' (x y : JSString) (h : x ≠ y) : strLt x y = true ∨ strLt y x = true := strLt_total x y h

theorem boolFirst_trans (x y z : Bool) (h1 : (x && !y) = true) (h2 : (y && !z) = true) : (x && !z) = true := by
  cases x <;> cases y <;> cases z <;> simp_all
theorem boolFirst_total (x y : Bool) (h : x ≠ y) : (x && !y) = true ∨ (y && !x) = true := by
  cases x <;> cases y <;> simp_all

/-! ## Links as the readable definitions spell them -/

section
variable {α : Type} {rest : α → α → Int}

theorem CmpLaws.neThen {β : Type} [DecidableEq β] [BEq β] [LawfulBEq β] (key : α → β) (lt : β → β → Bool)
    (irrefl : ∀ x, lt x x = false) (trans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true)
    (total : ∀ x y, x ≠ y → lt x y = true ∨ lt y x = true) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if lt (key a) (key b) then -1 else 1) else rest a b) :=
  (CmpLaws.keyThen key lt irrefl trans total hr).congr fun a b => by
    by_cases e : key a = key b <;> simp [e]

theorem CmpLaws.intAsc (key : α → Int) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if decide (key a < key b) then -1 else 1) else rest a b) :=
  CmpLaws.neThen key (fun x y => decide (x < y)) intLt_irrefl intLt_trans intLt_total hr

theorem CmpLaws.intDesc (key : α → Int) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if decide (key a > key b) then -1 else 1) else rest a b) :=
  CmpLaws.neThen key (fun x y => decide (x > y)) intGt_irrefl intGt_trans intGt_total hr

theorem CmpLaws.strAsc (key : α → JSString) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if strLt (key a) (key b) then -1 else 1) else rest a b) :=
  CmpLaws.neThen key strLt strLt_irrefl strLt_trans strLt_total' hr

theorem CmpLaws.strDesc (key : α → JSString) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if strLt (key b) (key a) then -1 else 1) else rest a b) :=
  CmpLaws.neThen key (fun x y => strLt y x) (fun x => strLt_irrefl x) strGt_trans
    (fun x y h => strLt_total' y x (Ne.symm h)) hr

theorem CmpLaws.trueFirst (key : α → Bool) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if key a = true then -1 else 1) else rest a b) :=
  (CmpLaws.neThen key (fun x y => x && !y) (by simp) boolFirst_trans boolFirst_total hr).congr fun a b => by
    cases key a <;> cases key b <;> simp

theorem CmpLaws.trueLast (key : α → Bool) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if (key a != key b) = true then (if key a = true then 1 else -1) else rest a b) :=
  (CmpLaws.neThen key (fun x y => !x && y) (by simp) (by intro x y z; cases x <;> cases y <;> cases z <;> simp)
    (by intro x y; cases x <;> cases y <;> simp) hr).congr fun a b => by
    cases key a <;> cases key b <;> simp

theorem CmpLaws.intCmp (key : α → Int) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if decide (key a < key b) then -1 else if decide (key b < key a) then 1 else rest a b) :=
  CmpLaws.threeWay key (fun x y => decide (x < y)) intLt_irrefl intLt_trans intLt_total hr

theorem CmpLaws.intCmpDesc (key : α → Int) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if decide (key a > key b) then -1 else if decide (key b > key a) then 1 else rest a b) :=
  CmpLaws.threeWay key (fun x y => decide (x > y)) intGt_irrefl intGt_trans intGt_total hr

theorem CmpLaws.strCmp (key : α → JSString) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if strLt (key a) (key b) then -1 else if strLt (key b) (key a) then 1 else rest a b) :=
  CmpLaws.threeWay key strLt strLt_irrefl strLt_trans strLt_total' hr

theorem CmpLaws.strCmpDesc (key : α → JSString) (hr : CmpLaws rest) :
    CmpLaws (fun a b => if strLt (key b) (key a) then -1 else if strLt (key a) (key b) then 1 else rest a b) :=
  CmpLaws.threeWay key (fun x y => strLt y x) (fun x => strLt_irrefl x) strGt_trans
    (fun x y h => strLt_total' y x (Ne.symm h)) hr

end

/-- Proves `CmpLaws cmp` for a comparator written as a chain of keys (see the module docs). -/
macro "cmp_laws" : tactic => `(tactic| repeat' first
  | exact CmpLaws.zero
  | exact CmpLaws.sub _
  | exact CmpLaws.subRev _
  | apply CmpLaws.trueFirst
  | apply CmpLaws.trueLast
  | apply CmpLaws.intAsc
  | apply CmpLaws.intDesc
  | apply CmpLaws.strAsc
  | apply CmpLaws.strDesc
  | apply CmpLaws.intCmp
  | apply CmpLaws.intCmpDesc
  | apply CmpLaws.strCmp
  | apply CmpLaws.strCmpDesc)

end Ariadne

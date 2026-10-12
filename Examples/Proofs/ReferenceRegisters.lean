import Examples.ShallowReference.registers
import Init.Data.Order.PackageFactories
import Init.Data.Order.LemmasExtra
set_option backward.dsimp.instances true
namespace Examples.Proofs.ReferenceRegisters
open Ariadne Ariadne.Shallow Extracted_reference_registers.Shallow
abbrev State := NativeTypes.«Registers#state»
def key (a b : JSString) : JSString := a ++ [0] ++ b

def write (s : State) (k : JSString) (v : Int) (t : JSString) : State :=
  if s.stamps.get k |>.any (fun old => compare t old != .gt) then s
  else { s with values := s.values.set k v, stamps := s.stamps.set k t }

def count (s : State) (k : JSString) (v : Int) : State :=
  if (s.counters.get k).getD 0 < v then { s with counters := s.counters.set k v } else s

theorem write_eq (s : State) (a b : JSString) (v : Int) (t : JSString) :
    («Registers#write» s a b v t).2.1 = write s (key a b) v t := by
  cases h : s.stamps.get (key a b) <;> simp +instances [«Registers#write», write, key] at h ⊢
  all_goals rw [h] <;> simp <;> split <;> simp_all +instances

theorem count_eq (s : State) (a b : JSString) (v : Int) :
    («Registers#count» s a b v).2.1 = count s (key a b) v := by
  change (if decide ((s.counters.get (key a b)).elim 0 (fun x => x) < v) then
    ((), { s with counters := s.counters.set (key a b) v }, ()) else ((), s, ())).2.1 = _
  have e : (s.counters.get (key a b)).elim 0 (fun x => x) = (s.counters.get (key a b)).getD 0 := by
    cases s.counters.get (key a b) <;> rfl
  rw [e]
  by_cases h : (s.counters.get (key a b)).getD 0 < v <;> simp [count, h]

theorem read_eq (s : State) (a b : JSString) :
    «Registers#read» s a b = s.values.get (key a b) := rfl

theorem counter_eq (s : State) (a b : JSString) :
    «Registers#counter» s a b = (s.counters.get (key a b)).getD 0 := by
  cases h : s.counters.get (key a b) <;> simp +instances [«Registers#counter», key] at h ⊢
  all_goals rw [h]; rfl

theorem write_idempotent (s : State) (k : JSString) (v : Int) (t : JSString) :
    write (write s k v t) k v t = write s k v t := by
  unfold write
  split
  · simp_all +instances
  · simp

theorem count_idempotent (s : State) (k : JSString) (v : Int) :
    count (count s k v) k v = count s k v := by
  unfold count
  split
  · simp
  · simp_all +instances


structure Stamp where
  text : JSString
instance : Ord Stamp := ⟨compareOn Stamp.text⟩
instance : Std.TransOrd Stamp := inferInstanceAs (Std.TransCmp (compareOn Stamp.text))
instance : Std.LawfulEqOrd Stamp where
  eq_of_compare {a b} h := by
    have e : a.text = b.text := Std.LawfulEqOrd.eq_of_compare h
    cases a; cases b; simp_all +instances
instance : Std.LinearOrderPackage Stamp := .ofOrd Stamp

def newer (old : Option JSString) (t : JSString) : Bool :=
  old.any (fun seen => compare t seen != .gt)

def slot (old : Option JSString × Option Int) (v : Int) (t : JSString) : Option JSString × Option Int :=
  if newer old.1 t then old else (some t, some v)

theorem slot_swap (old : Option JSString × Option Int) (v w : Int) (t u : JSString)
    (consistent : t = u → v = w) :
    slot (slot old v t) w u = slot (slot old w u) v t := by
  have order (a b : JSString) : (compare a b != Ordering.gt) = decide (¬ (Stamp.mk b < Stamp.mk a)) := by
    apply Bool.eq_iff_iff.mpr
    simp +instances only [bne_iff_ne, decide_eq_true_eq]
    exact not_congr (Std.compare_eq_gt (a := Stamp.mk a) (b := Stamp.mk b))
  rcases old with ⟨old, value⟩
  cases old with
  | none =>
    simp +instances only [slot, newer, Option.any_none, Option.any_some, order, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
    split <;> split
    all_goals simp +instances only [Std.not_lt] at *
    all_goals grind [Stamp.mk.injEq, Std.le_antisymm, Std.le_trans, Std.le_total]
  | some old =>
    by_cases ht : Stamp.mk old < Stamp.mk t
    all_goals by_cases hu : Stamp.mk old < Stamp.mk u
    all_goals simp +instances [slot, newer, order, ht, hu]
    all_goals repeat' split
    all_goals simp +instances only [Std.not_lt] at *
    all_goals grind [Stamp.mk.injEq, Std.le_antisymm, Std.le_trans, Std.le_total]


def countSlot (old : Option Int) (v : Int) : Option Int :=
  if old.getD 0 < v then some v else old

theorem countSlot_swap (old : Option Int) (v w : Int) :
    countSlot (countSlot old v) w = countSlot (countSlot old w) v := by
  cases old <;> simp +instances only [countSlot, Option.getD_none, Option.getD_some]
  all_goals split <;> split
  all_goals try simp_all +instances only [Option.getD_some]
  all_goals repeat' split
  all_goals simp_all +instances <;> omega

inductive Operation where
  | write (a b : JSString) (value : Int) (stamp : JSString)
  | count (a b : JSString) (value : Int)

def applyOp (s : State) : Operation → State
  | .write a b v t => («Registers#write» s a b v t).2.1
  | .count a b v => («Registers#count» s a b v).2.1

abbrev View := (Option JSString × Option Int) × Option Int

def view (s : State) (q : JSString) : View := ((s.stamps.get q, s.values.get q), s.counters.get q)

def transition (q : JSString) (old : View) : Operation → View
  | .write a b v t => if key a b = q then (slot old.1 v t, old.2) else old
  | .count a b v => if key a b = q then (old.1, countSlot old.2 v) else old

theorem view_write (s : State) (k q : JSString) (v : Int) (t : JSString) :
    view (write s k v t) q = if k = q then (slot (view s q).1 v t, (view s q).2) else view s q := by
  by_cases eq : k = q
  · subst k; simp +instances only [write, view, slot, newer, ↓reduceIte]
    split <;> simp_all +instances
  · simp +instances only [write]; split <;> simp +instances [view, eq, JSMap.get_set]

theorem view_count (s : State) (k q : JSString) (v : Int) :
    view (count s k v) q = if k = q then ((view s q).1, countSlot (view s q).2 v) else view s q := by
  by_cases eq : k = q
  · subst k; simp +instances only [count, view, countSlot, ↓reduceIte]
    split <;> simp_all +instances only [JSMap.get_set_self, ite_true, ite_false]
  · simp +instances only [count]; split <;> simp +instances [view, eq, JSMap.get_set]

theorem view_apply (s : State) (q : JSString) (op : Operation) :
    view (applyOp s op) q = transition q (view s q) op := by
  cases op <;> simp +instances only [applyOp, write_eq, count_eq, view_write, view_count, transition]

def Compatible : Operation → Operation → Prop
  | .write a b v t, .write c d w u => key a b = key c d → t = u → v = w
  | _, _ => True

theorem transition_swap (q : JSString) (old : View) (x y : Operation) (consistent : Compatible x y) :
    transition q (transition q old x) y = transition q (transition q old y) x := by
  cases x <;> cases y
  all_goals rename_i a b v t
  all_goals simp +instances only [transition]
  all_goals repeat' split
  all_goals simp_all +instances [slot_swap, countSlot_swap, Compatible]

private theorem view_fold (ops : List Operation) (s : State) (q : JSString) :
    view (ops.foldl applyOp s) q = ops.foldl (transition q) (view s q) := by
  induction ops generalizing s with
  | nil => rfl
  | cons x xs ih => simp +instances only [List.foldl_cons, ih, view_apply]

theorem convergence (xs ys : List Operation) (permutation : xs.Perm ys)
    (consistent : ∀ x ∈ xs, ∀ y ∈ xs, Compatible x y) (s : State) (q : JSString) :
    view (xs.foldl applyOp s) q = view (ys.foldl applyOp s) q := by
  rw [view_fold, view_fold]
  exact permutation.foldl_eq' (fun x hx y hy old => transition_swap q old x y (consistent x hx y hy)) _

theorem idempotence (s : State) (op : Operation) : applyOp (applyOp s op) op = applyOp s op := by
  cases op <;> simp +instances only [applyOp, write_eq, count_eq, write_idempotent, count_idempotent]

theorem read_convergence (xs ys : List Operation) (permutation : xs.Perm ys)
    (consistent : ∀ x ∈ xs, ∀ y ∈ xs, Compatible x y) (s : State) (a b : JSString) :
    «Registers#read» (xs.foldl applyOp s) a b = «Registers#read» (ys.foldl applyOp s) a b := by
  simpa only [read_eq, view] using congrArg (fun x : View => x.1.2)
    (convergence xs ys permutation consistent s (key a b))

theorem counter_convergence (xs ys : List Operation) (permutation : xs.Perm ys)
    (consistent : ∀ x ∈ xs, ∀ y ∈ xs, Compatible x y) (s : State) (a b : JSString) :
    «Registers#counter» (xs.foldl applyOp s) a b = «Registers#counter» (ys.foldl applyOp s) a b := by
  simpa only [counter_eq, view] using congrArg (fun x : View => x.2.getD 0)
    (convergence xs ys permutation consistent s (key a b))
end Examples.Proofs.ReferenceRegisters


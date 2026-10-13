import Ariadne.Shallow.Adequacy.WP

/-!
Heap facts for weakest-precondition proofs about concrete source bodies:
reading through appends and writes, binding assignment, iterating an array and
the dense-array length bound of literals and spreads.
-/

namespace Ariadne

theorem bound_of_some {heap : Heap} {i : Nat} {o : Object} (h : heap[i]? = some o) : i < heap.length :=
  (List.getElem?_eq_some_iff.mp h).choose

theorem getElem_of_some {heap : Heap} {i : Nat} {o : Object} (h : heap[i]? = some o) :
    ∃ bound : i < heap.length, heap[i] = o :=
  ⟨(List.getElem?_eq_some_iff.mp h).choose, (List.getElem?_eq_some_iff.mp h).choose_spec⟩

/-- A heap that keeps every object of another is at least as long. -/
theorem length_le_of_agree {heap heap' : Heap} (agree : ∀ i, i < heap.length → heap'[i]? = heap[i]?) :
    heap.length ≤ heap'.length := by
  rcases heap.eq_nil_or_concat with h | ⟨init, last, rfl⟩
  · simp [h]
  · have same := agree init.length (by simp)
    have last : heap'[init.length]? = some last := by simpa using same
    have := bound_of_some last
    (try simp); omega

theorem assign_eq {s : State} {name other : String} {loc : Nat} {v : Value}
    (find : s.env.find? (fun p => p.1 == name) = some (other, loc)) (bound : loc < s.heap.length) :
    s.assign name v = .ok { s with heap := s.heap.set loc (.cell v) } := by
  simp [State.assign, find, State.write, bound, bind, Except.bind, pure, Except.pure]

theorem iterable_array {s : State} {l : Nat} {xs : List Value} (h : s.heap[l]? = some (.array xs)) :
    iterable s (.ref l) = .ok (xs, s) := by
  simp [iterable, h, pure, Except.pure]

theorem array_bound {xs : List Value} {p : Prop} (bound : xs.length < 4294967296) (h : p) :
    xs.length < 4294967296 ∧ p := ⟨bound, h⟩

theorem zero_scientific : Float.Model.ofScientific 0 0 = Float.Model.ofInt 0 := by kernel_rfl
theorem one_scientific : Float.Model.ofScientific 1 0 = Float.Model.ofInt 1 := by kernel_rfl
theorem zero_literal : Value.ofLiteral (.number 0 0) = .number (Float.Model.ofInt 0) := by kernel_rfl
theorem ofNat_ofInt (n : Nat) : Float.Model.ofNat n = Float.Model.ofInt n := rfl

/-- A natural number below a safe integer is a safe integer. -/
theorem Shallow.Int53.nat_range {k n : Nat} (le : k ≤ n) (range : Shallow.Int53.InRange (n : Int)) :
    Shallow.Int53.InRange (k : Int) := by
  rw [Shallow.Int53.range_iff_natAbs] at *
  simp at *
  omega

/-- Arithmetic side conditions about heap lengths. Sequenced with `;` so a
failed attempt fails the discharge instead of being recovered. -/
macro "heap_arith" : tactic =>
  `(tactic| (first | omega | (simp only [List.length_append, List.length_set, List.length_cons, List.length_nil]; omega)))

/-- Heap reads through appends and writes, side conditions discharged arithmetically. -/
macro "heap_simp" : tactic => `(tactic| (simp (disch := heap_arith) only [List.getElem?_set_ne, List.getElem?_set_self,
  List.getElem?_append_left, List.getElem?_append_right, List.length_append, List.length_set, List.length_cons,
  List.length_nil, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
  Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.zero_add, ne_eq,
  Option.some.injEq] at *))

end Ariadne

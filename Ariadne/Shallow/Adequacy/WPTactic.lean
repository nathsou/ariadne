import Ariadne.Shallow.Adequacy.WPAttr
import Ariadne.Shallow.Adequacy.WP
import Ariadne.Shallow.Adequacy.WPHeap
import Ariadne.Shallow.Adequacy.WPData
import Ariadne.Shallow.Adequacy.WPRecord

/-!
Automation for weakest-precondition proofs about concrete source bodies.
`wp` applies one rule per syntactic node; `wp_eval` discharges the lookups and
primitive operations that rules leave behind. Both only build proofs that the
kernel checks; they never assume a step.
-/

namespace Ariadne

/-- Lookup and operator side conditions of a concrete source body. -/
macro "wp_eval" : tactic => `(tactic| (simp +arith [*, wp_simps, Shallow.Adequacy.bindArguments, State.declare,
  State.alloc, State.lookup, State.assign, State.write, readMember, readIndex, iterable, List.getElem?_append,
  List.getElem?_set, List.find?_cons, binary, unary, Value.ofLiteral, strictEqual, Value.truthy, literalCase,
  pure, Except.pure, bind, Except.bind]; try rfl))

/-- The same side conditions without arithmetic normalization, which can loop
on integer comparisons. -/
macro "wp_eval_plain" : tactic => `(tactic| (simp [*, wp_simps, Shallow.Adequacy.bindArguments, State.declare,
  State.alloc, State.lookup, State.assign, State.write, readMember, readIndex, iterable, List.getElem?_append,
  List.getElem?_set, List.find?_cons, binary, unary, Value.ofLiteral, strictEqual, Value.truthy, literalCase,
  pure, Except.pure, bind, Except.bind] <;> rfl))

/-- Reduce decided conditions in the goal. -/
macro "wp_reduce" : tactic => `(tactic| (simp only [*, wp_simps, Value.truthy, strictEqual, literalCase,
  Value.ofLiteral, decide_true, decide_false, gt_iff_lt, ge_iff_le, Option.map_none, Option.map_some,
  Option.getD_none, Option.getD_some, List.drop_zero, List.drop_succ_cons, List.flatMap_cons, List.flatMap_nil,
  List.append_nil, ↓reduceIte, reduceCtorEq, Bool.not_true, Bool.not_false, Bool.false_eq_true, bne_iff_ne,
  ne_eq, bne_self_eq_false, not_true_eq_false, not_false_eq_true, Bool.true_or, Bool.false_or, Bool.or_true,
  Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Completion.leaveSwitch,
  beq_self_eq_true]))

/-- The array a builtin call reads: allocated by an earlier step, so the read
goes through appends rather than through the whole context, where arithmetic
normalization can loop. -/
macro "wp_lookup" : tactic => `(tactic| first
  | (simp (disch := heap_arith) only [State.alloc, List.getElem?_set_ne, List.getElem?_set_self,
      List.getElem?_append_left, List.getElem?_append_right, List.length_append, List.length_set, List.length_cons,
      List.length_nil, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
      Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.zero_add,
      Option.some.injEq, Object.array.injEq]; first | done | rfl)
  | wp_eval_plain
  | wp_eval)

/-- One weakest-precondition step for the node at the head of the goal, with
`t` discharging lookups and evaluations. -/
syntax "wp_step_by " "(" tacticSeq ")" : tactic

macro_rules
  | `(tactic| wp_step_by ($t)) => `(tactic| first
  | refine WPS.block ?_
  | refine WPB.nil ?_
  | refine WPB.cons ?_
  | refine WPS.return_ ?_
  | refine WPS.let_ ?_
  | refine WPS.expr ?_
  | refine WPS.if_ ?_
  | refine WPS.assignVar ?_
  | refine WPS.switch_ ?_
  | refine WPS.break_ ?_
  | refine WPS.continue_ ?_
  | refine WPE.literal ?_
  | refine WPE.var (by $t) ?_
  | refine WPE.call ?_
  | refine WPE.member ?_
  | refine WPE.index ?_
  | refine WPE.and ?_
  | refine WPE.or ?_
  | refine WPE.coalesce ?_
  | refine WPE.binary (by decide) ?_
  | refine WPE.unary ?_
  | refine WPE.conditional ?_
  | refine WPA.nil ?_
  | refine WPA.cons ?_
  | refine WPI.map_get (by $t) ?_
  | refine WPI.map_has (by $t) ?_
  | refine WPI.map_set (by $t) ?_
  | refine WPI.map_delete (by $t) ?_
  | refine WPI.array_slice (by $t) ?_
  | refine WPI.array_filter (by $t) ?_
  | refine WPE.array ?_
  | refine WPElements.nil ?_
  | refine WPElements.spread ?_
  | refine WPElements.single (by intro _ _ h; cases h) ?_
  | refine WPE.lambda ?_
  | refine array_bound (by first | omega | (simp; done) | (simp; omega)) ?_
  | refine ⟨_, _, iterable_array (by $t), ?_⟩
  | refine ⟨_, SelectsCase.literals rfl, ?_⟩
  | refine ⟨_, by $t, ?_⟩
  | (rw [if_pos (by assumption)])
  | (rw [if_neg (by assumption)])
  | wp_reduce)

/-- One weakest-precondition step for the node at the head of the goal. -/
macro "wp_step" : tactic => `(tactic| wp_step_by (wp_eval))

macro "wp" : tactic => `(tactic| repeat wp_step)

/-- Evaluation side conditions of generated proofs: first without arithmetic
normalization, which keeps comparisons in the form the native callbacks state
and cannot loop, then with it. -/
macro "wp_eval_data" : tactic => `(tactic| first | wp_eval_plain | wp_eval)

/-- `wp` for generated proofs: it also steps through the array builtins whose
callbacks the generated invariants cover. The builtin rules stay out of
`wp_step`, where their failed attempts slow down the reference proofs. It stops
at the postcondition, a conjunction, rather than letting evaluation attempts
search the whole context for it, and only reduces its decided conditions. -/
macro "wp_data" : tactic => `(tactic| (repeat ((fail_if_success (show _ ∧ _)); first
    | refine WPI.array_map (by wp_lookup) ?_
    | refine WPI.array_reduce (by wp_lookup) ?_
    | refine WPI.array_search (mode := "some") (Or.inl rfl) (by wp_lookup) ?_
    | refine WPI.array_search (mode := "every") (Or.inr (Or.inl rfl)) (by wp_lookup) ?_
    | refine WPI.array_search (mode := "find") (Or.inr (Or.inr (Or.inl rfl))) (by wp_lookup) ?_
    | refine WPI.array_toReversed (by wp_lookup) ?_
    | refine WPE.record ?_
    | refine WPFields.nil ?_
    | refine WPFields.cons (by decide) ?_
    | wp_step_by (wp_eval_data)) <;> try wp_reduce))

set_option hygiene false in
/-- A state reached from the function's bound arguments by allocations and
callback traversals keeps the bound arguments' heap. The latest traversal's
invariant is named `kept`. -/
macro "frames_auto" : tactic => `(tactic| repeat (first
  | exact Frames.refl _
  | exact Kept.frames (by assumption)
  | exact Frames.heap_eq kept.frames rfl
  | apply Frames.alloc))

set_option hygiene false in
/-- Close a callback specification after stepping through its body: the call
completed, returned the specified value, kept the invariant (named `kept`) and
restored the caller's bindings. -/
macro "callback_close" : tactic => `(tactic| (
  refine ⟨Or.inr trivial, by first | rfl | (simp; done) | (simp; omega), ?_, by first | rfl | trivial | simp⟩
  try simp only [List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    State.declare, State.alloc] at *
  first
    | exact Kept.heap_eq kept rfl
    | exact Kept.append kept _ _
    | (simp only [List.append_assoc, List.cons_append, List.nil_append]; exact Kept.append kept _ _)))

end Ariadne

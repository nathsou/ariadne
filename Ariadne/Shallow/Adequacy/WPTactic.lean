import Ariadne.Shallow.Adequacy.WPAttr
import Ariadne.Shallow.Adequacy.WP

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

/-- Reduce decided conditions in the goal. -/
macro "wp_reduce" : tactic => `(tactic| (simp only [*, wp_simps, Value.truthy, strictEqual, literalCase,
  Value.ofLiteral, decide_true, decide_false, gt_iff_lt, ge_iff_le, Option.map_none, Option.map_some,
  Option.getD_none, Option.getD_some, List.drop_zero, List.drop_succ_cons, List.flatMap_cons, List.flatMap_nil,
  List.append_nil, ↓reduceIte, reduceCtorEq, Bool.not_true, Bool.not_false, Bool.false_eq_true, bne_iff_ne,
  ne_eq, bne_self_eq_false, not_true_eq_false, not_false_eq_true, Bool.true_or, Bool.false_or, Bool.or_true,
  Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Completion.leaveSwitch,
  beq_self_eq_true]))

/-- One weakest-precondition step for the node at the head of the goal. -/
macro "wp_step" : tactic => `(tactic| first
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
  | refine WPE.var (by wp_eval) ?_
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
  | refine WPI.map_get (by wp_eval) ?_
  | refine WPI.map_has (by wp_eval) ?_
  | refine WPI.map_set (by wp_eval) ?_
  | refine WPI.map_delete (by wp_eval) ?_
  | refine WPI.array_slice (by wp_eval) ?_
  | refine ⟨_, SelectsCase.literals rfl, ?_⟩
  | refine ⟨_, by wp_eval, ?_⟩
  | (rw [if_pos (by assumption)])
  | (rw [if_neg (by assumption)])
  | wp_reduce)

macro "wp" : tactic => `(tactic| repeat wp_step)

end Ariadne

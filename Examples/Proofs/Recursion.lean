import Examples.Recursive.countdown

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Examples.Recursion
open Ariadne
open Recursive_countdown (compiled_definitions)

/-- The proof permits any external-call handler. In particular, this program's
recursive execution does not rely on the reference-call compatibility branch. -/
private theorem countdown_nat (count : Nat) (external : Target.Runtime)
    (extraDepth extraFuel : Nat) (before : State) :
    ∃ after,
      Target.link external compiled_definitions (extraDepth + count + 1)
        (extraFuel + 8 * count + 12) before (.function "countdown") [.bigint count] =
        .ok (.bigint count, after) ∧ after.env = before.env := by
  induction count generalizing before with
  | zero =>
    simp [Target.link, compiled_definitions, Target.function, Target.scope,
      Target.sequence, Target.branch, Target.binary, Target.read, Target.literal,
      Target.return_, State.declare, State.alloc, State.lookup,
      Value.ofLiteral, Value.truthy, binary, bind, pure, Except.pure, Except.bind,
      bne, BEq.beq, instBEqControl.beq, Control.ctorIdx]
  | succ count ih =>
    have positive : ¬((count : Int) + 1 ≤ 0) := by omega
    simp only [Nat.mul_succ, ← Nat.add_assoc, Nat.add_one]
    rw [Target.link.eq_2]
    simp [compiled_definitions, Target.function, Target.scope,
      Target.sequence, Target.branch, Target.binary, Target.read, Target.literal,
      Target.return_, Target.empty, Target.call, Target.consArg, Target.noArgs,
      State.declare, State.alloc, State.lookup, Value.ofLiteral, Value.truthy,
      binary, bind, pure, Except.pure, Except.bind,
      bne, BEq.beq, instBEqControl.beq, Control.ctorIdx, positive]
    obtain ⟨after, executed, _⟩ := ih {
      env := [("count", before.heap.length)]
      heap := before.heap ++ [.cell (.bigint ((count : Int) + 1))] }
    simp only [compiled_definitions, Nat.add_assoc] at executed
    simp only [Nat.add_assoc]
    rw [executed]
    simp [Int.add_comm]

/-- An arbitrary handler, even one that always fails, suffices: recursion follows
only the certified named-function table. Negative inputs return immediately. -/
theorem countdown_without_external_calls (count : Int) (external : Target.Runtime) :
    (Target.link external compiled_definitions (8 * count.toNat + 12)
      (8 * count.toNat + 12) {} (.function "countdown") [.bigint count]).map Prod.fst =
      .ok (.bigint (max count 0)) := by
  cases count with
  | ofNat n =>
    obtain ⟨after, executed, _⟩ := countdown_nat n external (7 * n + 11) 0 {}
    have depth : 7 * n + 11 + n + 1 = 8 * n + 12 := by omega
    simpa [depth, Int.max_eq_left (Int.natCast_nonneg n), executed, Except.map] using
      congrArg (fun result => result.map Prod.fst) executed
  | negSucc n =>
    have nonpositive : Int.negSucc n ≤ 0 := by omega
    simp [Target.link, compiled_definitions, Target.function, Target.scope,
      Target.sequence, Target.branch, Target.binary, Target.read, Target.literal,
      Target.return_, State.declare, State.alloc, State.lookup, Value.ofLiteral,
      Value.truthy, binary, bind, pure, Except.pure, Except.bind, Except.map,
      bne, BEq.beq, instBEqControl.beq, Control.ctorIdx, nonpositive, Int.max_eq_right nonpositive]

theorem countdown_correct (count : Int) :
    Recursive_countdown.compiled_ts_countdown (8 * count.toNat + 12) [.bigint count] =
      .ok (.bigint (max count 0)) :=
  countdown_without_external_calls count (apply Recursive_countdown.program)

theorem countdown_source (count : Int) :
    SourceReturns Recursive_countdown.source "countdown" [.bigint count] (.bigint (max count 0)) :=
  Recursive_countdown.compiled_source (countdown_correct count)

theorem countdown_larger_budget (count : Int) (fuel : Nat)
    (enough : 8 * count.toNat + 12 ≤ fuel) :
    Recursive_countdown.compiled_ts_countdown fuel [.bigint count] =
      .ok (.bigint (max count 0)) := by
  have stable := run_fuel_mono Recursive_countdown.program "countdown" [.bigint count] enough
  change (Recursive_countdown.ts_countdown _ _).Refines (Recursive_countdown.ts_countdown _ _) at stable
  rw [← Recursive_countdown.compiled_correct, countdown_correct] at stable
  exact (stable.eq_of_completed (by intro h; cases h)).symm

theorem countdown_unique_result (count : Int) (result : Value)
    (h : SourceReturns Recursive_countdown.source "countdown" [.bigint count] result) :
    result = .bigint (max count 0) :=
  h.deterministic (countdown_source count)

end Examples.Recursion

import Ariadne.Convergence

namespace Ariadne

/-- Statement execution in the original evaluator, including control and final state. -/
def ExecutesStatement (program : Program) (before : State) (statement : Stmt) (out : Completion) : Prop :=
  Converges (fun fuel => exec program fuel before statement) (.ok out)

def ExecutesBlock (program : Program) (before : State) (statements : List Stmt) (out : Completion) : Prop :=
  Converges (fun fuel => execBlock program fuel before statements) (.ok out)

/-- Compound updates evaluate the receiver and key once, read the old value,
then evaluate the right operand and write into its resulting heap. -/
def UpdatesTarget (program : Program) (before : State) (target : Expr)
    (op : String) (rhs : Expr) (after : State) : Prop :=
  Converges (fun fuel => updateTarget program fuel before target op rhs) (.ok after)

theorem UpdatesTarget.eventually {program : Program} {before after : State}
    {target rhs : Expr} {op : String} (h : UpdatesTarget program before target op rhs after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → updateTarget program fuel before target op rhs = .ok after :=
  ((converges_iff_eventually _ (fun h => updateTarget_fuel_mono program h before target op rhs) _).mp h).2

theorem ExecutesStatement.update {program : Program} {before after : State}
    {target rhs : Expr} {op : String}
    (updated : UpdatesTarget program before target op rhs after) (span : Span) :
    ExecutesStatement program before (.update target op rhs span) {state := after} := by
  obtain ⟨_, fuel, written⟩ := updated
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [exec, written, bind, Except.bind, pure, Except.pure]

theorem UpdatesTarget.record {program : Program} {before selected operated after : State}
    {receiver rhs : Expr} {address : Nat} {field op : String} {old delta value : Value}
    {fields : List (String × Value)}
    (selectedReceiver : Evaluates program before receiver (.ref address) selected)
    (read : readMember selected (.ref address) field = .ok old)
    (operand : Evaluates program selected rhs delta operated)
    (operation : binary op old delta = .ok value)
    (object : operated.heap[address]? = some (.record fields))
    (write : operated.write address (.record (fieldSet fields field value)) = .ok after)
    (span : Span) : UpdatesTarget program before (.member receiver field span) op rhs after := by
  obtain ⟨nr, hr⟩ := selectedReceiver.eventually
  obtain ⟨nd, hd⟩ := operand.eventually
  refine ⟨(by intro h; cases h), max nr nd + 1, ?_⟩
  simp [updateTarget, hr _ (Nat.le_max_left ..), hd _ (Nat.le_max_right ..),
    read, operation, object, write, bind, Except.bind]

theorem ExecutesStatement.eventually {program : Program} {before : State} {statement : Stmt} {out : Completion}
    (h : ExecutesStatement program before statement out) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → exec program fuel before statement = .ok out :=
  ((converges_iff_eventually _ (fun h => exec_fuel_mono program h before statement) _).mp h).2

theorem ExecutesBlock.eventually {program : Program} {before : State} {statements : List Stmt} {out : Completion}
    (h : ExecutesBlock program before statements out) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → execBlock program fuel before statements = .ok out :=
  ((converges_iff_eventually _ (fun h => execBlock_fuel_mono program h before statements) _).mp h).2

theorem ExecutesStatement.return_ {program : Program} {before after : State} {expression : Expr} {value : Value}
    (h : Evaluates program before expression value after) (span : Span) :
    ExecutesStatement program before (.return_ expression span) { control := .returned, value, state := after } := by
  obtain ⟨_, fuel, evaluated⟩ := h
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [exec, evaluated, bind, Except.bind, pure, Except.pure]

theorem ExecutesStatement.let_ {program : Program} {before after : State} {expression : Expr} {value : Value}
    (h : Evaluates program before expression value after) (mutable : Bool) (name : String) (annotation : Option Ty) (span : Span) :
    ExecutesStatement program before (.let_ mutable name annotation expression span)
      { state := after.declare name value } := by
  obtain ⟨_, fuel, evaluated⟩ := h
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [exec, evaluated, bind, Except.bind, pure, Except.pure]

theorem ExecutesStatement.if_ {program : Program} {before tested : State} {condition : Expr} {test : Value}
    {yes no : Stmt} {out : Completion} (conditionEval : Evaluates program before condition test tested)
    (branch : ExecutesStatement program tested (if test.truthy then yes else no) out) (span : Span) :
    ExecutesStatement program before (.if_ condition yes no span) out := by
  obtain ⟨nc, hc⟩ := conditionEval.eventually
  obtain ⟨nb, hb⟩ := branch.eventually
  refine ⟨(by intro h; cases h), max nc nb + 1, ?_⟩
  simpa [exec, hc _ (Nat.le_max_left ..), bind, Except.bind, pure, Except.pure]
    using hb _ (Nat.le_max_right nc nb)

theorem ExecutesBlock.nil (program : Program) (state : State) : ExecutesBlock program state [] { state } :=
  ⟨(by intro h; cases h), 1, rfl⟩

private theorem controlBeq (a b : Control) : (a == b) = decide (a = b) := by cases a <;> cases b <;> rfl

theorem ExecutesBlock.stop {program : Program} {before : State} {statement : Stmt} {out : Completion}
    (head : ExecutesStatement program before statement out) (rest : List Stmt) (stopped : out.control ≠ .normal) :
    ExecutesBlock program before (statement :: rest) out := by
  obtain ⟨_, fuel, executed⟩ := head
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [execBlock, executed, bne, controlBeq, stopped, bind, Except.bind, pure, Except.pure]

theorem ExecutesBlock.next {program : Program} {before : State} {statement : Stmt} {rest : List Stmt}
    {head out : Completion} (first : ExecutesStatement program before statement head) (normal : head.control = .normal)
    (tail : ExecutesBlock program head.state rest out) : ExecutesBlock program before (statement :: rest) out := by
  obtain ⟨nh, hh⟩ := first.eventually
  obtain ⟨nt, ht⟩ := tail.eventually
  refine ⟨(by intro h; cases h), max nh nt + 1, ?_⟩
  simpa [execBlock, hh _ (Nat.le_max_left ..), bne, controlBeq, normal, bind, Except.bind, pure, Except.pure]
    using ht _ (Nat.le_max_right nh nt)

theorem ExecutesStatement.block {program : Program} {before : State} {statements : List Stmt} {out : Completion}
    (body : ExecutesBlock program before statements out) (span : Span) :
    ExecutesStatement program before (.block statements span)
      { out with state := { out.state with env := before.env } } := by
  obtain ⟨_, fuel, executed⟩ := body
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [exec, executed, bind, Except.bind, pure, Except.pure]

/-- Appending a continuation has no effect after a non-normal completion. -/
theorem ExecutesBlock.append_stopped {program : Program} {before : State} {statements : List Stmt} {out : Completion}
    (body : ExecutesBlock program before statements out) (stopped : out.control ≠ .normal) (rest : List Stmt) :
    ExecutesBlock program before (statements ++ rest) out := by
  obtain ⟨_, fuel, executed⟩ := body
  have step : ∀ fuel before statements, execBlock program fuel before statements = .ok out →
      execBlock program fuel before (statements ++ rest) = .ok out := by
    intro fuel
    induction fuel with
    | zero => intro before statements impossible; cases impossible
    | succ fuel ih =>
      intro before statements executed
      cases statements with
      | nil => simp [execBlock, pure, Except.pure] at executed; subst out; contradiction
      | cons statement statements =>
        simp only [List.cons_append, execBlock] at executed ⊢
        cases head : exec program fuel before statement with
        | error fault => simp [head, bind, Except.bind] at executed
        | ok first =>
          simp only [head, bind, Except.bind] at executed ⊢
          by_cases stoppedFirst : (first.control != Control.normal) = true
          · simpa only [stoppedFirst, ↓reduceIte] using executed
          · simp only [stoppedFirst] at executed ⊢
            exact ih first.state statements executed
  exact ⟨(by intro h; cases h), fuel, step fuel before statements executed⟩

/-- A convergent sequence exposes its first completion and the continuation
only when that completion is normal. -/
theorem ExecutesBlock.cons_inv {program : Program} {before : State} {statement : Stmt}
    {rest : List Stmt} {out : Completion} (h : ExecutesBlock program before (statement :: rest) out) :
    ∃ first, ExecutesStatement program before statement first ∧
      ((first.control ≠ .normal ∧ first = out) ∨
        (first.control = .normal ∧ ExecutesBlock program first.state rest out)) := by
  obtain ⟨_, fuel, executed⟩ := h
  cases fuel with
  | zero => cases executed
  | succ fuel =>
    change (exec program fuel before statement).bind (fun first =>
      if first.control != .normal then .ok first else execBlock program fuel first.state rest) = .ok out at executed
    cases head : exec program fuel before statement with
    | error fault => simp [head, Except.bind] at executed
    | ok first =>
      refine ⟨first, ⟨(by intro h; cases h), fuel, head⟩, ?_⟩
      simp only [head, Except.bind, bne, controlBeq] at executed
      by_cases normal : first.control = .normal
      · right
        exact ⟨normal, (by intro h; cases h), fuel, by simpa [normal] using executed⟩
      · left
        exact ⟨normal, by simpa [normal] using executed⟩

theorem ExecutesBlock.if_ {program : Program} {before tested : State} {condition : Expr} {test : Value}
    {yes no : Stmt} {rest : List Stmt} {out : Completion}
    (conditionEval : Evaluates program before condition test tested)
    (branch : ExecutesBlock program tested ((if test.truthy then yes else no) :: rest) out) (span : Span) :
    ExecutesBlock program before (.if_ condition yes no span :: rest) out := by
  obtain ⟨first, head, stopped | normal⟩ := branch.cons_inv
  · rw [← stopped.2]
    exact ExecutesBlock.stop (ExecutesStatement.if_ conditionEval head span) rest stopped.1
  · exact ExecutesBlock.next (ExecutesStatement.if_ conditionEval head span) normal.1 normal.2

end Ariadne

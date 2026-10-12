import Ariadne.Fuel

namespace Ariadne

/-- Successful evaluation in the existing operational semantics, without a
budget in the statement used by a compositional correctness proof. -/
def Evaluates (program : Program) (before : State) (expression : Expr)
    (value : Value) (after : State) : Prop :=
  Converges (fun fuel => evalExpr program fuel before expression) (.ok (value, after))

theorem Evaluates.eventually {program : Program} {before after : State} {expression : Expr} {value : Value}
    (h : Evaluates program before expression value after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → evalExpr program fuel before expression = .ok (value, after) :=
  ((converges_iff_eventually _ (fun h => evalExpr_fuel_mono program h before expression) _).mp h).2

theorem Evaluates.literal (program : Program) (state : State) (value : Literal) (span : Span) :
    Evaluates program state (.literal value span) (Value.ofLiteral value) state :=
  ⟨(by intro h; cases h), 1, rfl⟩

theorem State.lookup_present {state : State} {name : String} {value : Value}
    (lookup : state.lookup name = .ok value) : state.env.any (fun p => p.1 == name) = true := by
  cases found : state.env.find? (fun p => p.1 == name) with
  | none => simp [State.lookup, found, throw] at lookup
  | some entry =>
    exact List.any_eq_true.mpr ⟨entry, List.mem_of_find?_eq_some found, List.find?_some (p := fun p : String × Nat => p.1 == name) found⟩

theorem Evaluates.variable (program : Program) (state : State) (name : String) (span : Span) (value : Value)
    (present : state.env.any (fun p => p.1 == name) = true) (lookup : state.lookup name = .ok value) :
    Evaluates program state (.var name span) value state := by
  refine ⟨(by intro h; cases h), 1, ?_⟩
  simp [evalExpr, present, lookup, bind, Except.bind, pure, Except.pure]

theorem Evaluates.unary {program : Program} {before middle : State} {arg : Expr} {a value : Value}
    (input : Evaluates program before arg a middle) (op : String) (span : Span)
    (primitive : Ariadne.unary op a = .ok value) :
    Evaluates program before (.unary op arg span) value middle := by
  rcases input.2 with ⟨fuel, evaluated⟩
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [evalExpr, evaluated, primitive, bind, Except.bind, pure, Except.pure]

/-- Strict binary operations evaluate their operands in source order, possibly
with effects. Short-circuit operations have separate rules below. -/
theorem Evaluates.binary {program : Program} {before middle after : State}
    {left right : Expr} {a b value : Value}
    (hl : Evaluates program before left a middle) (hr : Evaluates program middle right b after)
    (op : String) (span : Span) (strict : op ≠ "&&" ∧ op ≠ "||" ∧ op ≠ "??")
    (primitive : Ariadne.binary op a b = .ok value) :
    Evaluates program before (.binary op left right span) value after := by
  rcases hl.eventually with ⟨nl, hl⟩
  rcases hr.eventually with ⟨nr, hr⟩
  refine ⟨(by intro h; cases h), max nl nr + 1, ?_⟩
  simp [evalExpr, hl _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), strict.1,
    strict.2.1, strict.2.2, primitive, bind, Except.bind, pure, Except.pure]

theorem Evaluates.conditional {program : Program} {before tested after : State}
    {condition yes no : Expr} {test value : Value}
    (hc : Evaluates program before condition test tested)
    (branch : Evaluates program tested (if test.truthy then yes else no) value after) (span : Span) :
    Evaluates program before (.conditional condition yes no span) value after := by
  rcases hc.eventually with ⟨nc, hc⟩
  rcases branch.eventually with ⟨nb, hb⟩
  refine ⟨(by intro h; cases h), max nc nb + 1, ?_⟩
  simpa [evalExpr, hc _ (Nat.le_max_left ..), bind, Except.bind, pure, Except.pure]
    using hb _ (Nat.le_max_right nc nb)

theorem Evaluates.and_false {program : Program} {before after : State}
    {left right : Expr} {value : Value} (hl : Evaluates program before left value after)
    (stop : value.truthy = false) (span : Span) :
    Evaluates program before (.binary "&&" left right span) value after := by
  rcases hl.2 with ⟨fuel, hl⟩
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [evalExpr, hl, stop, bind, Except.bind, pure, Except.pure]

theorem Evaluates.or_true {program : Program} {before after : State}
    {left right : Expr} {value : Value} (hl : Evaluates program before left value after)
    (stop : value.truthy = true) (span : Span) :
    Evaluates program before (.binary "||" left right span) value after := by
  rcases hl.2 with ⟨fuel, hl⟩
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [evalExpr, hl, stop, bind, Except.bind, pure, Except.pure]

theorem Evaluates.and_true {program : Program} {before middle after : State}
    {left right : Expr} {a value : Value}
    (hl : Evaluates program before left a middle) (hr : Evaluates program middle right value after)
    (go : a.truthy = true) (span : Span) :
    Evaluates program before (.binary "&&" left right span) value after := by
  rcases hl.eventually with ⟨nl, hl⟩
  rcases hr.eventually with ⟨nr, hr⟩
  refine ⟨(by intro h; cases h), max nl nr + 1, ?_⟩
  simp [evalExpr, hl _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), go, bind, Except.bind, pure, Except.pure]

theorem Evaluates.or_false {program : Program} {before middle after : State}
    {left right : Expr} {a value : Value}
    (hl : Evaluates program before left a middle) (hr : Evaluates program middle right value after)
    (go : a.truthy = false) (span : Span) :
    Evaluates program before (.binary "||" left right span) value after := by
  rcases hl.eventually with ⟨nl, hl⟩
  rcases hr.eventually with ⟨nr, hr⟩
  refine ⟨(by intro h; cases h), max nl nr + 1, ?_⟩
  simp [evalExpr, hl _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), go, bind, Except.bind, pure, Except.pure]

theorem Evaluates.member {program : Program} {before after : State} {receiver : Expr} {a value : Value}
    (input : Evaluates program before receiver a after) (field : String) (span : Span)
    (read : readMember after a field = .ok value) :
    Evaluates program before (.member receiver field span) value after := by
  rcases input.2 with ⟨fuel, input⟩
  refine ⟨(by intro h; cases h), fuel + 1, ?_⟩
  simp [evalExpr, input, read, bind, Except.bind, pure, Except.pure]

theorem Evaluates.index {program : Program} {before middle after : State}
    {receiver index : Expr} {a i value : Value}
    (hr : Evaluates program before receiver a middle) (hi : Evaluates program middle index i after)
    (span : Span) (read : readIndex after a i = .ok value) :
    Evaluates program before (.index receiver index span) value after := by
  rcases hr.eventually with ⟨nr, hr⟩
  rcases hi.eventually with ⟨ni, hi⟩
  refine ⟨(by intro h; cases h), max nr ni + 1, ?_⟩
  simp [evalExpr, hr _ (Nat.le_max_left ..), hi _ (Nat.le_max_right ..), read, bind, Except.bind, pure, Except.pure]

end Ariadne

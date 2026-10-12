import Ariadne.Target

namespace Ariadne.Target

/-- A call interface makes recursive linking independent of source syntax. -/
abbrev Runtime := Nat → State → Value → List Value → Result (Value × State)
abbrev Arguments := Nat → State → Result (List Value × State)

/-- Agreement on a finite prefix of the runtime budget. -/
def Agree (limit : Nat) (left right : Nat → α) : Prop :=
  ∀ fuel, fuel ≤ limit → left fuel = right fuel

namespace Agree

theorem refl (f : Nat → α) : Agree limit f f := fun _ _ => rfl

theorem mono (h : Agree large f g) (le : small ≤ large) : Agree small f g :=
  fun fuel bound => h fuel (Nat.le_trans bound le)

end Agree

/-- A fragment never consults a call budget larger than its own budget. -/
def Causal (code : Runtime → Nat → α) : Prop :=
  ∀ limit left right, Agree limit left right → Agree limit (code left) (code right)

def noArgs : Arguments
  | 0, _ => .error .timeout
  | _ + 1, s => .ok ([], s)

def consArg (first : Expression) (rest : Arguments) : Arguments
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (value, s) ← first n s
    let (values, s) ← rest n s
    return (value :: values, s)

/-- Callee, then arguments from left to right, then dispatch, exactly as in the
source evaluator. Arguments can themselves call functions and allocate frames. -/
def call (runtime : Runtime) (callee : Expression) (args : Arguments) : Expression
  | 0, _ => .error .timeout
  | n + 1, s => do
    let (fn, s) ← callee n s
    let (values, s) ← args n s
    runtime n s fn values

theorem unary_congr (h : Agree limit a b) : Agree limit (unary op a) (unary op b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [unary, h n (by omega)]

theorem binary_congr (hl : Agree limit a b) (hr : Agree limit c d) :
    Agree limit (binary op a c) (binary op b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [binary, hl n (by omega), hr n (by omega)]

theorem conditional_congr (hg : Agree limit a b) (hy : Agree limit c d)
    (hn : Agree limit e f) : Agree limit (conditional a c e) (conditional b d f) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n =>
    simp only [conditional, hg n (by omega)]
    congr 1; funext pair
    split <;> simp_all only [hy n (by omega), hn n (by omega)]

theorem member_congr (h : Agree limit a b) : Agree limit (member a field) (member b field) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [member, h n (by omega)]

theorem index_congr (ha : Agree limit a b) (hi : Agree limit c d) :
    Agree limit (index a c) (index b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [index, ha n (by omega), hi n (by omega)]

theorem consArg_congr (ha : Agree limit a b) (hs : Agree limit c d) :
    Agree limit (consArg a c) (consArg b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [consArg, ha n (by omega), hs n (by omega)]

theorem call_congr (hr : Agree limit r t) (hf : Agree limit a b) (ha : Agree limit c d) :
    Agree limit (call r a c) (call t b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [call, hr n (by omega), hf n (by omega), ha n (by omega)]

theorem sequence_congr (ha : Agree limit a b) (hb : Agree limit c d) :
    Agree limit (sequence a c) (sequence b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [sequence, ha n (by omega), hb n (by omega)]

theorem scope_congr (h : Agree limit a b) : Agree limit (scope a) (scope b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [scope, h n (by omega)]

theorem declare_congr (h : Agree limit a b) : Agree limit (declare name a) (declare name b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [declare, h n (by omega)]

theorem assign_congr (h : Agree limit a b) : Agree limit (assign name a) (assign name b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => simp only [assign, h n (by omega)]

theorem discard_congr (h : Agree limit a b) : Agree limit (discard a) (discard b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [discard, h n (by omega)]

theorem branch_congr (hg : Agree limit a b) (hy : Agree limit c d)
    (hn : Agree limit e f) : Agree limit (branch a c e) (branch b d f) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n =>
    simp only [branch, hg n (by omega)]
    congr 1; funext pair
    split <;> simp_all only [hy n (by omega), hn n (by omega)]

def AgreeUpdate (limit : Nat) : Option Command → Option Command → Prop
  | none, none => True
  | some a, some b => Agree limit a b
  | _, _ => False

theorem loop_congr (hg : Agree limit a b) (hb : Agree limit c d)
    (hu : AgreeUpdate limit u v) : Agree limit (loop a c u) (loop b d v) := by
  intro fuel le; funext s
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [loop, hg n (by omega), hb n (by omega)]
    have recurse := fun s => ih (by omega) s
    cases u <;> cases v <;> simp only [AgreeUpdate] at hu
    · simp only [recurse]
    · simp only [hu n (by omega), recurse]

theorem while_congr (hg : Agree limit a b) (hb : Agree limit c d) :
    Agree limit (while_ a c) (while_ b d) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => exact congrFun (loop_congr hg hb (u := none) (v := none) trivial n (by omega)) s

theorem for_congr (hi : Agree limit a b) (hg : Agree limit c d)
    (hu : Agree limit e f) (hb : Agree limit g h) :
    Agree limit (for_ a c e g) (for_ b d f h) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n =>
    simp only [for_, hi n (by omega), loop_congr hg hb (u := some e) (v := some f) hu n (by omega)]

theorem return_congr (h : Agree limit a b) : Agree limit (return_ a) (return_ b) := by
  intro fuel le; funext s
  cases fuel with
  | zero => rfl
  | succ n => simp only [return_, h n (by omega)]

/-- A function frame needs only the body's strictly smaller fuel prefix. -/
theorem function_congr (h : Agree limit a b) (bound : fuel ≤ limit + 2) :
    function ps a fuel = function ps b fuel := by
  funext s args
  cases fuel with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => simp only [function, h n (by omega)]

end Ariadne.Target

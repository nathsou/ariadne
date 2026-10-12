import Ariadne.Kernel
import Ariadne.Value

namespace Ariadne.Shallow.Int53

def limit : Int := 9007199254740991

abbrev InRange (value : Int) : Prop := -limit ≤ value ∧ value ≤ limit

def inRange (value : Int) : Bool := decide (InRange value)

@[simp] theorem inRange_iff (value : Int) : inRange value = true ↔ InRange value := by
  simp [inRange]

theorem zero_inRange : InRange 0 := by decide

theorem neg_inRange {value : Int} (valid : InRange value) : InRange (-value) := by
  unfold InRange at *
  omega

/-- Bit equality is deliberate: numeric equality would identify +0 and -0. -/
def exact (actual : Float.Model) (expected : Int) : Bool :=
  actual.toBits == (Float.Model.ofInt expected).toBits

theorem exact_iff (actual : Float.Model) (expected : Int) :
    exact actual expected = true ↔ actual = Float.Model.ofInt expected := by
  simp only [exact, beq_iff_eq]
  constructor
  · intro equal
    have ext : ∀ a b : Float.Model, a.toBits = b.toBits → a = b := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      cases h
      rfl
    exact ext _ _ equal
  · intro equal
    exact congrArg Float.Model.toBits equal

/-- A range-only multiplication claim would lose the sign of this result. -/
theorem negative_zero_not_exact : exact (Float.Model.ofInt (-1) * Float.Model.ofInt 0) 0 = false := by
  kernel_rfl

theorem negated_zero_not_exact : exact (-Float.Model.ofInt 0) 0 = false := by
  kernel_rfl

end Ariadne.Shallow.Int53

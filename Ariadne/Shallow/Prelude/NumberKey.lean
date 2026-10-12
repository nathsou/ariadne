import Ariadne.Shallow.Prelude.Map

namespace Ariadne.Shallow.NumberKey
open Float.Model

/-- IEEE equality with the NaN case needed for Map and Set keys. Kept separate
from the global IEEE BEq instance used by source `===`. -/
def equal (a b : Float.Model) : Bool := (a.isNaN && b.isNaN) || a == b

@[instance_reducible] def equality : BEq Float.Model := ⟨equal⟩

private inductive View where
  | nan | zero
  | infinity (sign : UnpackedFloat.Sign)
  | finite (sign : UnpackedFloat.Sign) (mantissa : Nat) (exponent : Int)
  deriving DecidableEq

private def view : UnpackedFloat → View
  | .notANumber => .nan
  | .zero _ => .zero
  | .infinity sign => .infinity sign
  | .finite sign mantissa exponent _ => .finite sign mantissa exponent

private theorem unpacked_equal_iff (a b : UnpackedFloat) :
    ((a.isNaN && b.isNaN) || a.beq b) = true ↔ view a = view b := by
  rcases a with ⟨(_ | _)⟩ | _ | ⟨(_ | _)⟩ | ⟨(_ | _), ma, ea, ha⟩ <;>
    rcases b with ⟨(_ | _)⟩ | _ | ⟨(_ | _)⟩ | ⟨(_ | _), mb, eb, hb⟩
  all_goals simp [view, UnpackedFloat.isNaN, UnpackedFloat.beq, UnpackedFloat.compare, and_comm]
  all_goals rfl

instance equiv : @EquivBEq Float.Model equality := by
  letI : BEq Float.Model := equality
  apply equivBEq_of_iff_apply_eq (fun a => view a.unpack)
  intro a b
  exact unpacked_equal_iff a.unpack b.unpack

@[simp] theorem equal_refl (a : Float.Model) : equal a a = true :=
  @BEq.refl Float.Model equality equiv.toReflBEq a

theorem equal_symmetric (a b : Float.Model) : equal a b = equal b a :=
  @BEq.comm Float.Model equality equiv.toPartialEquivBEq a b

theorem equal_transitive {a b c : Float.Model}
    (ab : equal a b = true) (bc : equal b c = true) : equal a c = true :=
  @BEq.trans Float.Model equality equiv.toPartialEquivBEq a b c ab bc

theorem agrees_with_operational (a b : Float.Model) :
    equal a b = Ariadne.sameValueZero (.number a) (.number b) := rfl

/-- Keys stored or yielded by native Maps/Sets always use positive zero. -/
def normalize (a : Float.Model) : Float.Model :=
  if a == Float.Model.ofNat 0 then Float.Model.ofNat 0 else a

theorem normalize_equal (a b : Float.Model) : equal (normalize a) b = equal a b := by
  unfold normalize
  split
  · rename_i h
    have same : equal a (Float.Model.ofNat 0) = true := by simp [equal, h]
    exact (@BEq.congr_left Float.Model equality equiv.toPartialEquivBEq a (Float.Model.ofNat 0) b same).symm
  · rfl

@[simp] theorem normalize_idempotent (a : Float.Model) : normalize (normalize a) = normalize a := by
  unfold normalize
  split <;> rfl

theorem normalize_agrees_with_operational (a : Float.Model) :
    Value.number (normalize a) = canonicalKey (.number a) := rfl

theorem nan_strict_inequality : (Float.Model.nan == Float.Model.nan) = false := rfl

theorem zero_key_equality : equal (-(Float.Model.ofNat 0)) (Float.Model.ofNat 0) = true := rfl

theorem normalize_negative_zero : normalize (-(Float.Model.ofNat 0)) = Float.Model.ofNat 0 := rfl

end Ariadne.Shallow.NumberKey

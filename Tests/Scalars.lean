import Ariadne

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Tests.Scalars
open Ariadne

theorem negative_bigint_division : binary "/" (.bigint (-17)) (.bigint 5) = .ok (.bigint (-3)) := by kernel_rfl

theorem negative_bigint_remainder : binary "%" (.bigint (-17)) (.bigint 5) = .ok (.bigint (-2)) := by kernel_rfl

theorem zero_bigint_division :
    binary "/" (.bigint 1) (.bigint 0) = .error (.rangeError "bigint division by zero") := by kernel_rfl

theorem trunc_preserves_negative_zero :
    invokeScalar "Math.trunc" [.number (-(Float.Model.ofNat 0))] =
      .ok (.number (-(Float.Model.ofNat 0))) := by kernel_rfl

theorem nan_strictly_unequal : strictEqual (.number Float.Model.nan) (.number Float.Model.nan) = false := by kernel_rfl

theorem nan_map_key_equal : sameValueZero (.number Float.Model.nan) (.number Float.Model.nan) = true := by kernel_rfl

theorem negative_zero_key_canonical :
    canonicalKey (.number (-(Float.Model.ofNat 0))) = .number (Float.Model.ofNat 0) := by kernel_rfl

theorem utf16_lexicographic_order :
    binary "<" (.string [55357, 56832]) (.string [65535]) = .ok (.boolean true) := by kernel_rfl

theorem string_slice_negative_index :
    invokeString [65, 55357, 56832] "slice" [.number (Float.Model.ofInt (-1))] =
      .ok (.string [56832]) := by kernel_rfl

theorem bigint_conversion_rejects_fraction :
    invokeScalar "BigInt" [.number (Float.Model.ofScientific 15 (-1))] =
      .error (.rangeError "BigInt requires a finite integer") := by kernel_rfl

end Tests.Scalars

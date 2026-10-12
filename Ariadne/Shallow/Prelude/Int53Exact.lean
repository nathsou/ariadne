import Ariadne.Shallow.Prelude.Int53
import Ariadne.Builtins
set_option maxHeartbeats 400000
namespace Ariadne.Shallow.Int53
open Float.Model Float.Model.UnpackedFloat

private theorem log2_shift (n k : Nat) (positive : 0 < n) : (n <<< k).log2 = n.log2 + k := by
  rw [Nat.shiftLeft_eq]
  induction k with
  | zero => simp
  | succ k ih =>
    have nonzero : n * 2 ^ k ≠ 0 := Nat.ne_of_gt (Nat.mul_pos positive (Nat.two_pow_pos k))
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (n * 2 ^ k) 2, Nat.log2_two_mul nonzero, ih]
    omega

private theorem target_canonical (m : Nat) (e : Int) (bits : m.log2 = 52) (lower : -1074 ≤ e) :
    Format.binary64.targetExponent (totalExponent m e) = e := by
  simp only [Format.targetExponent, totalExponent, bits, Format.mantissaBits, Format.minExponent]
  omega

private theorem shift_same (m : Nat) (e : Int) :
    shiftToExponent m e .exact e = (⟨m, false, false⟩, e) := by
  simp [shiftToExponent, ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]

private theorem round_canonical (sign : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) (bits : m.log2 = 52) (lower : -1074 ≤ e) :
    roundWithAccuracy Format.binary64 sign m e .exact = .finite sign m e positive := by
  simp only [roundWithAccuracy, shiftToTargetExponent, target_canonical m e bits lower, shift_same,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]
  simp [Nat.ne_of_gt positive]

private theorem round_integer (sign : Sign) (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 53) :
    round Format.binary64 sign n 0 =
      .finite sign (n <<< (52 - n.log2)) (-(((52 - n.log2 : Nat) : Int)))
        (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  have bits : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound; omega
  have target : Format.binary64.targetExponent (totalExponent n 0) = -(((52 - n.log2 : Nat) : Int)) := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  unfold round
  rw [target]
  simp only [decreaseExponent, Int.zero_sub, Int.neg_neg, Int.toNat_natCast]
  exact round_canonical sign (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int)) (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _))
    (by rw [log2_shift n _ positive]; omega) (by omega)

private theorem unpackSign_components (sign : Sign) (exponent : BitVec 11) (mantissa : BitVec 52) :
    unpackSign (packComponents Format.binary64 sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have zero : i = 0 := by omega
  subst i
  simp only [unpackSign, packComponents, BitVec.getElem_extractLsb']
  simp only [BitVec.getLsbD_append]
  simp [BitVec.getLsbD_eq_getElem]

private theorem unpack_pack_normal (sign : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) (bits : m.log2 = 52) (lower : -1074 ≤ e) (upper : e ≤ 971) :
    (Float.Model.pack (.finite sign m e positive)).unpack = .finite sign m e positive := by
  have mbounds : 2 ^ 52 ≤ m ∧ m < 2 ^ 53 := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp bits
  let biased := (e + 1075).toNat
  have bpos : 0 < biased := by dsimp [biased]; omega
  have bbound : biased < 2047 := by dsimp [biased]; omega
  have bzero : BitVec.ofNat 11 biased ≠ 0#11 := by
    intro h
    have h := congrArg BitVec.toNat h
    simp at h
    omega
  have binf : BitVec.ofNat 11 biased ≠ -1#11 := by
    intro h
    have h := congrArg BitVec.toNat h
    simp at h
    omega
  have expEq : ((BitVec.ofNat 11 biased).toNat : Int) - (1023 + 52) = e := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    dsimp [biased]
    omega
  have mantEq : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    change (BitVec.cons true (BitVec.ofNat 52 m)).toNat = m
    rw [BitVec.toNat_cons']
    simp only [Bool.toNat_true, Nat.one_shiftLeft, BitVec.toNat_ofNat]
    omega
  have signEq : Sign.ofBitVec sign.toBitVec = sign := by cases sign <;> rfl
  simp only [Float.Model.pack, Float.Model.unpack, UInt64.toBitVec_ofBitVec, UnpackedFloat.pack,
    Format.exponentBias, Format.mantissaBits, bits]
  have biasedEq : (e + ((2 ^ (11 - 1) - 1 : Nat) : Int) + ((52 : Nat) : Int)).toNat = biased := by
    dsimp [biased]
    congr 1
    omega
  rw [biasedEq]
  simp only [ite_true]
  rw [ite_eq_right (by omega)]
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_components, bzero, binf, ↓reduceIte, signEq]
  congr 1

private theorem ofInt_signed (sign : Sign) (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 53) :
    Float.Model.ofInt (sign.apply (n : Int)) =
      Float.Model.pack (.finite sign (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int))
        (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _))) := by
  have pos : (0 : Int) < n := by omega
  have neg : -(n : Int) < 0 := by omega
  cases sign
  all_goals simp only [Sign.apply, Float.Model.ofInt, UnpackedFloat.ofInt, normalize,
    Int.compare_eq_ite_lt, pos, neg, Int.neg_neg, Int.toNat_natCast, ↓reduceIte, round_integer _ n positive bound]
  all_goals rfl

private theorem unpack_ofInt_signed (sign : Sign) (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 53) :
    (Float.Model.ofInt (sign.apply (n : Int))).unpack =
      .finite sign (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int))
        (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  rw [ofInt_signed sign n positive bound]
  apply unpack_pack_normal
  · have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound
    rw [log2_shift n _ positive]
    omega
  · omega
  · omega

private def canonicalCompare (n m : Nat) : Ordering :=
  (compare (-((52 - n.log2 : Nat) : Int)) (-((52 - m.log2 : Nat) : Int))).then
    (compare (n <<< (52 - n.log2)) (m <<< (52 - m.log2)))

private theorem canonicalCompare_lt (n m : Nat) (npos : 0 < n) (mpos : 0 < m)
    (nbound : n < 2 ^ 53) (mbound : m < 2 ^ 53) (lt : n < m) : canonicalCompare n m = .lt := by
  have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt npos)).mpr nbound; omega
  have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mpos)).mpr mbound; omega
  have mono : n.log2 ≤ m.log2 := (Nat.le_log2 (Nat.ne_of_gt mpos)).mpr
    (Nat.le_trans (Nat.log2_self_le (Nat.ne_of_gt npos)) (Nat.le_of_lt lt))
  by_cases same : n.log2 = m.log2
  · have scaled : n <<< (52 - m.log2) < m <<< (52 - m.log2) := by
      simp only [Nat.shiftLeft_eq]
      exact Nat.mul_lt_mul_of_pos_right lt (Nat.two_pow_pos _)
    simp only [canonicalCompare, same, Std.ReflOrd.compare_self, Ordering.eq_then]
    exact Nat.compare_eq_lt.mpr scaled
  · have exp : -((52 - n.log2 : Nat) : Int) < -((52 - m.log2 : Nat) : Int) := by omega
    simp [canonicalCompare, Int.compare_eq_lt.mpr exp]

private theorem canonicalCompare_swap (n m : Nat) :
    (canonicalCompare n m).swap = canonicalCompare m n := by
  simp only [canonicalCompare, Ordering.swap_then, Int.compare_swap, Nat.compare_swap]

private theorem canonicalCompare_eq (n m : Nat) (npos : 0 < n) (mpos : 0 < m)
    (nbound : n < 2 ^ 53) (mbound : m < 2 ^ 53) : canonicalCompare n m = compare n m := by
  rcases Nat.lt_trichotomy n m with lt | rfl | gt
  · rw [canonicalCompare_lt n m npos mpos nbound mbound lt, Nat.compare_eq_lt.mpr lt]
  · simp [canonicalCompare]
  · rw [← canonicalCompare_swap m n, canonicalCompare_lt m n mpos npos mbound nbound gt]
    exact (Nat.compare_eq_gt.mpr gt).symm

private theorem safe_cases (a : Int) (safe : InRange a) : a = 0 ∨
    ∃ sign : Sign, ∃ n : Nat, 0 < n ∧ n < 2 ^ 53 ∧ a = sign.apply (n : Int) := by
  rcases safe with ⟨lo, hi⟩
  unfold limit at lo hi
  cases a with
  | ofNat n =>
    change -limit ≤ (n : Int) at lo
    change (n : Int) ≤ limit at hi
    unfold limit at lo hi
    by_cases zero : n = 0
    · left; simp [zero]
    · right; exact ⟨.positive, n, by omega, by omega, rfl⟩
  | negSucc n =>
    right
    exact ⟨.negative, n + 1, by omega, by omega, by simp [Sign.apply, Int.negSucc_eq]⟩

private theorem unpack_zero : (Float.Model.ofInt 0).unpack = .zero .positive := by kernel_rfl

private theorem compare_signed (sa sb : Sign) (n m : Nat) (npos : 0 < n) (mpos : 0 < m)
    (nbound : n < 2 ^ 53) (mbound : m < 2 ^ 53) :
    Float.Model.compare (Float.Model.ofInt (sa.apply (n : Int))) (Float.Model.ofInt (sb.apply (m : Int))) =
      some (compare (sa.apply (n : Int)) (sb.apply (m : Int))) := by
  unfold Float.Model.compare
  rw [unpack_ofInt_signed sa n npos nbound, unpack_ofInt_signed sb m mpos mbound]
  cases sa <;> cases sb
  · change some (canonicalCompare n m).swap = some (compare (-(n : Int)) (-(m : Int)))
    rw [canonicalCompare_eq n m npos mpos nbound mbound, Nat.compare_swap]
    simp [Int.compare_eq_ite_lt, Nat.compare_eq_ite_lt]
  · simp (disch := omega) [UnpackedFloat.compare, Sign.apply, Int.compare_eq_ite_lt] <;> grind
  · simp (disch := omega) [UnpackedFloat.compare, Sign.apply, Int.compare_eq_ite_lt] <;> grind
  · change some (canonicalCompare n m) = some (compare (n : Int) (m : Int))
    rw [canonicalCompare_eq n m npos mpos nbound mbound]
    simp [Int.compare_eq_ite_lt, Nat.compare_eq_ite_lt]

/-- Integer comparison agrees with binary64 comparison throughout the safe range. -/
theorem compare_ofInt (a b : Int) (ha : InRange a) (hb : InRange b) :
    Float.Model.compare (Float.Model.ofInt a) (Float.Model.ofInt b) = some (compare a b) := by
  rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · kernel_rfl
    · unfold Float.Model.compare
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      cases sb <;> simp (disch := omega) [UnpackedFloat.compare, Sign.apply, Int.compare_eq_ite_lt] <;> grind
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · unfold Float.Model.compare
      rw [unpack_zero, unpack_ofInt_signed sa n np nb]
      cases sa <;> simp (disch := omega) [UnpackedFloat.compare, Sign.apply, Int.compare_eq_ite_lt] <;> grind
    · exact compare_signed sa sb n m np mp nb mb

theorem lt_ofInt (a b : Int) (ha : InRange a) (hb : InRange b) :
    Float.Model.ofInt a < Float.Model.ofInt b ↔ a < b := by
  change ((Float.Model.ofInt a).unpack.compare (Float.Model.ofInt b).unpack == some .lt) = true ↔ _
  change (Float.Model.compare (Float.Model.ofInt a) (Float.Model.ofInt b) == some .lt) = true ↔ _
  rw [compare_ofInt a b ha hb]
  simp [Int.compare_eq_lt]

theorem le_ofInt (a b : Int) (ha : InRange a) (hb : InRange b) :
    Float.Model.ofInt a ≤ Float.Model.ofInt b ↔ a ≤ b := by
  change (Float.Model.compare (Float.Model.ofInt a) (Float.Model.ofInt b)).any Ordering.isLE = true ↔ _
  rw [compare_ofInt a b ha hb]
  simp [Int.isLE_compare]

theorem beq_ofInt (a b : Int) (ha : InRange a) (hb : InRange b) :
    (Float.Model.ofInt a == Float.Model.ofInt b) = (a == b) := by
  change (Float.Model.compare (Float.Model.ofInt a) (Float.Model.ofInt b) == some .eq) = (a == b)
  rw [compare_ofInt a b ha hb]
  apply Bool.eq_iff_iff.mpr
  simp

theorem ofInt_injective (a b : Int) (ha : InRange a) (hb : InRange b) :
    Float.Model.ofInt a = Float.Model.ofInt b ↔ a = b := by
  constructor
  · intro eq
    have comparison := compare_ofInt a b ha hb
    rw [eq, compare_ofInt b b hb hb, Std.ReflOrd.compare_self] at comparison
    exact Int.compare_eq_eq.mp (Option.some.inj comparison).symm
  · exact congrArg Float.Model.ofInt

theorem neg_exact (a : Int) (safe : InRange a) (nonzero : a ≠ 0) :
    Float.Model.ofInt (-a) = -Float.Model.ofInt a := by
  rcases safe_cases a safe with zero | ⟨sign, n, positive, bound, rfl⟩
  · exact False.elim (nonzero zero)
  · have changeSign : -(sign.apply (n : Int)) = (-sign).apply (n : Int) := by cases sign <;> simp [Sign.apply]
    change _ = Float.Model.pack (Float.Model.ofInt (sign.apply (n : Int))).unpack.neg
    rw [changeSign, ofInt_signed (-sign) n positive bound, unpack_ofInt_signed sign n positive bound]
    rfl

theorem abs_exact (a : Int) (safe : InRange a) :
    Float.Model.ofInt (a.natAbs : Int) = (Float.Model.ofInt a).abs := by
  rcases safe_cases a safe with rfl | ⟨sign, n, positive, bound, rfl⟩
  · kernel_rfl
  · have absSign : (sign.apply (n : Int)).natAbs = n := by cases sign <;> simp [Sign.apply]
    change _ = Float.Model.pack (Float.Model.ofInt (sign.apply (n : Int))).unpack.abs
    rw [absSign, unpack_ofInt_signed sign n positive bound]
    exact ofInt_signed .positive n positive bound

private theorem extended_shift_exact (m k : Nat) :
    (ExtendedMantissa.mk (m <<< k) false false >>> k) = ExtendedMantissa.mk m false false := by
  induction k with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    change Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) ⟨m <<< (k + 1), false, false⟩ = _
    have repeat_next (f : ExtendedMantissa → ExtendedMantissa) (j : Nat) (x : ExtendedMantissa) : Nat.repeat f (j + 1) x = Nat.repeat f j (f x) := by
      induction j with
      | zero => rfl
      | succ j ih => exact congrArg f ih
    rw [repeat_next]
    have step : ExtendedMantissa.shiftRightOne ⟨m <<< (k + 1), false, false⟩ = ⟨m <<< k, false, false⟩ := by
      simp [ExtendedMantissa.shiftRightOne, Nat.shiftLeft_eq, Nat.pow_succ, ← Nat.mul_assoc]
    rw [step]
    exact ih

private theorem shift_scaled (m k : Nat) (e : Int) :
    shiftToExponent (m <<< k) (e - (k : Int)) .exact e = (⟨m, false, false⟩, e) := by
  have amount : (e - (e - (k : Int))).toNat = k := by omega
  simp only [shiftToExponent, amount, ExtendedMantissa.ofMantissaAndAccuracy, extended_shift_exact]
  congr 1
  omega

private theorem round_scaled (sign : Sign) (m k : Nat) (e : Int)
    (positive : 0 < m) (bits : m.log2 = 52) (lower : -1074 ≤ e) :
    roundWithAccuracy Format.binary64 sign (m <<< k) (e - (k : Int)) .exact = .finite sign m e positive := by
  have target : Format.binary64.targetExponent (totalExponent (m <<< k) (e - (k : Int))) = e := by
    simp only [Format.targetExponent, totalExponent, log2_shift m k positive, bits,
      Format.mantissaBits, Format.minExponent]
    omega
  simp only [roundWithAccuracy, shiftToTargetExponent, target, shift_scaled,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven,
    target_canonical m e bits lower, shift_same]
  simp [Nat.ne_of_gt positive]

private theorem round_shift (sign : Sign) (n k : Nat) (positive : 0 < n) (bound : n < 2 ^ 53) :
    round Format.binary64 sign (n <<< k) (-(k : Int)) = round Format.binary64 sign n 0 := by
  have bits : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound; omega
  let pad := 52 - n.log2
  have pos : 0 < n <<< pad := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)
  have mbits : (n <<< pad).log2 = 52 := by rw [log2_shift n pad positive]; dsimp [pad]; omega
  have low : -1074 ≤ -(pad : Int) := by dsimp [pad]; omega
  have target : Format.binary64.targetExponent (totalExponent (n <<< k) (-(k : Int))) = -(pad : Int) := by
    simp only [Format.targetExponent, totalExponent, log2_shift n k positive, Format.mantissaBits, Format.minExponent]
    dsimp [pad]
    omega
  rw [round_integer sign n positive bound]
  unfold round
  rw [target]
  by_cases kp : k ≤ pad
  · have amount : (-(k : Int) - -(pad : Int)).toNat = pad - k := by omega
    have mant : (n <<< k) <<< (pad - k) = n <<< pad := by rw [← Nat.shiftLeft_add]; congr 1; omega
    have exponent : -(k : Int) - ((pad - k : Nat) : Int) = -(pad : Int) := by omega
    simp only [decreaseExponent, amount, mant, exponent]
    exact round_canonical sign _ _ pos mbits low
  · have amount : (-(k : Int) - -(pad : Int)).toNat = 0 := by omega
    simp only [decreaseExponent, amount, Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero]
    have mant : (n <<< pad) <<< (k - pad) = n <<< k := by rw [← Nat.shiftLeft_add]; congr 1; omega
    have exponent : -(pad : Int) - ((k - pad : Nat) : Int) = -(k : Int) := by omega
    have h := round_scaled sign (n <<< pad) (k - pad) (-(pad : Int)) pos mbits low
    rw [mant, exponent] at h
    exact h

private theorem normalize_signed (sign : Sign) (n : Nat) (e : Int) (zeroSign : Sign) (positive : 0 < n) :
    normalize Format.binary64 (sign.apply (n : Int)) e zeroSign = round Format.binary64 sign n e := by
  have pos : (0 : Int) < n := by omega
  have neg : -(n : Int) < 0 := by omega
  have nonneg : ¬(n : Int) < 0 := by omega
  cases sign <;> simp only [normalize, Sign.apply, Int.compare_eq_ite_lt, pos, neg, nonneg,
    ↓reduceIte, Int.neg_neg, Int.toNat_natCast]

private theorem signed_scale (sign : Sign) (n k : Nat) :
    sign.apply ((n <<< k : Nat) : Int) = sign.apply (n : Int) * ((2 ^ k : Nat) : Int) := by
  cases sign <;> simp [Sign.apply, Nat.shiftLeft_eq, Int.natCast_mul, Int.neg_mul]

private theorem normalize_shift (a : Int) (safe : InRange a) (k : Nat) (zeroSign : Sign) :
    normalize Format.binary64 (a * ((2 ^ k : Nat) : Int)) (-(k : Int)) zeroSign =
      normalize Format.binary64 a 0 zeroSign := by
  rcases safe_cases a safe with rfl | ⟨sign, n, positive, bound, rfl⟩
  · simp [normalize]
  · rw [← signed_scale]
    rw [normalize_signed sign (n <<< k) _ zeroSign (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)),
      normalize_signed sign n _ zeroSign positive]
    exact round_shift sign n k positive bound

private theorem align_integer (n pad k : Nat) (larger : pad ≤ k) :
    decreaseExponent (n <<< pad) (-(pad : Int)) (-(k : Int)) = (n <<< k, -(k : Int)) := by
  have amount : (-(pad : Int) - -(k : Int)).toNat = k - pad := by omega
  simp only [decreaseExponent, amount, ← Nat.shiftLeft_add]
  have add : pad + (k - pad) = k := by omega
  rw [add]
  congr 1
  omega

/-- Addition of safe inputs is exact whenever its mathematical result is safe. -/
theorem add_exact (a b : Int) (ha : InRange a) (hb : InRange b) (sum : InRange (a + b)) :
    Float.Model.ofInt (a + b) = Float.Model.ofInt a + Float.Model.ofInt b := by
  rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · kernel_rfl
    · simp only [Int.zero_add]
      change _ = Float.Model.pack (UnpackedFloat.add Format.binary64 (Float.Model.ofInt 0).unpack _)
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      exact ofInt_signed sb m mp mb
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · simp only [Int.add_zero]
      change _ = Float.Model.pack (UnpackedFloat.add Format.binary64 _ (Float.Model.ofInt 0).unpack)
      rw [unpack_zero, unpack_ofInt_signed sa n np nb]
      exact ofInt_signed sa n np nb
    · change _ = Float.Model.pack (UnpackedFloat.add Format.binary64 _ _)
      rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
      let k := max (52 - n.log2) (52 - m.log2)
      have kn : 52 - n.log2 ≤ k := Nat.le_max_left _ _
      have km : 52 - m.log2 ≤ k := Nat.le_max_right _ _
      have small : min (-((52 - n.log2 : Nat) : Int)) (-((52 - m.log2 : Nat) : Int)) = -(k : Int) := by
        dsimp [k]
        omega
      simp only [UnpackedFloat.add, small, align_integer n _ k kn, align_integer m _ k km]
      rw [signed_scale sa n k, signed_scale sb m k, ← Int.add_mul,
        normalize_shift _ sum k .positive]
      rfl
theorem sub_exact (a b : Int) (ha : InRange a) (hb : InRange b) (difference : InRange (a - b)) :
    Float.Model.ofInt (a - b) = Float.Model.ofInt a - Float.Model.ofInt b := by
  rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · kernel_rfl
    · simp only [Int.zero_sub]
      change _ = Float.Model.pack (UnpackedFloat.sub Format.binary64 (Float.Model.ofInt 0).unpack _)
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      have changeSign : -(sb.apply (m : Int)) = (-sb).apply (m : Int) := by cases sb <;> simp [Sign.apply]
      rw [changeSign, ofInt_signed (-sb) m mp mb]
      rfl
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · simp only [Int.sub_zero]
      change _ = Float.Model.pack (UnpackedFloat.sub Format.binary64 _ (Float.Model.ofInt 0).unpack)
      rw [unpack_zero, unpack_ofInt_signed sa n np nb]
      exact ofInt_signed sa n np nb
    · change _ = Float.Model.pack (UnpackedFloat.sub Format.binary64 _ _)
      rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
      let k := max (52 - n.log2) (52 - m.log2)
      have kn : 52 - n.log2 ≤ k := Nat.le_max_left _ _
      have km : 52 - m.log2 ≤ k := Nat.le_max_right _ _
      have small : min (-((52 - n.log2 : Nat) : Int)) (-((52 - m.log2 : Nat) : Int)) = -(k : Int) := by
        dsimp [k]
        omega
      simp only [UnpackedFloat.sub, small, align_integer n _ k kn, align_integer m _ k km]
      rw [signed_scale sa n k, signed_scale sb m k, ← Int.sub_mul,
        normalize_shift _ difference k .positive]
      rfl

private theorem signed_bound (sign : Sign) (n : Nat) (safe : InRange (sign.apply (n : Int))) : n < 2 ^ 53 := by
  cases sign <;> simp [InRange, limit, Sign.apply] at safe <;> omega

private theorem signed_product (sa sb : Sign) (n m : Nat) :
    sa.apply (n : Int) * sb.apply (m : Int) = (sa * sb).apply ((n * m : Nat) : Int) := by
  cases sa <;> cases sb <;> simp [Sign.apply, Int.natCast_mul, Int.neg_mul, Int.mul_neg]

private theorem rounded_shift (sign : Sign) (n k : Nat) (positive : 0 < n) (bound : n < 2 ^ 53)
    (enough : 52 - n.log2 ≤ k) :
    roundWithAccuracy Format.binary64 sign (n <<< k) (-(k : Int)) .exact = round Format.binary64 sign n 0 := by
  let pad := 52 - n.log2
  have pos : 0 < n <<< pad := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)
  have mbits : (n <<< pad).log2 = 52 := by
    have := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound
    rw [log2_shift n pad positive]
    dsimp [pad]
    omega
  have mant : (n <<< pad) <<< (k - pad) = n <<< k := by rw [← Nat.shiftLeft_add]; congr 1; dsimp [pad]; omega
  have exponent : -(pad : Int) - ((k - pad : Nat) : Int) = -(k : Int) := by dsimp [pad]; omega
  rw [round_integer sign n positive bound]
  have h := round_scaled sign (n <<< pad) (k - pad) (-(pad : Int)) pos mbits (by dsimp [pad]; omega)
  rw [mant, exponent] at h
  exact h

/-- Zero operands must not acquire a negative IEEE sign. -/
def CanonicalProduct (a b : Int) : Prop := (a = 0 → 0 ≤ b) ∧ (b = 0 → 0 ≤ a)

theorem mul_exact (a b : Int) (ha : InRange a) (hb : InRange b) (product : InRange (a * b))
    (canonical : CanonicalProduct a b) :
    Float.Model.ofInt (a * b) = Float.Model.ofInt a * Float.Model.ofInt b := by
  rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · kernel_rfl
    · change _ = Float.Model.pack (UnpackedFloat.mul Format.binary64 (Float.Model.ofInt 0).unpack _)
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      have positive := canonical.1 rfl
      cases sb with
      | negative => simp [Sign.apply] at positive; omega
      | positive => simp only [Int.zero_mul]; rfl
  · rcases safe_cases b hb with rfl | ⟨sb, m, mp, mb, rfl⟩
    · change _ = Float.Model.pack (UnpackedFloat.mul Format.binary64 _ (Float.Model.ofInt 0).unpack)
      rw [unpack_zero, unpack_ofInt_signed sa n np nb]
      have positive := canonical.2 rfl
      cases sa with
      | negative => simp [Sign.apply] at positive; omega
      | positive => simp only [Int.mul_zero]; rfl
    · change _ = Float.Model.pack (UnpackedFloat.mul Format.binary64 _ _)
      rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
      have nmpos : 0 < n * m := Nat.mul_pos np mp
      have nmbound : n * m < 2 ^ 53 := by
        rw [signed_product] at product
        exact signed_bound _ _ product
      have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nb; omega
      have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mp)).mpr mb; omega
      have nle : n ≤ n * m := by exact Nat.le_mul_of_pos_right n mp
      have logn : n.log2 ≤ (n * m).log2 := (Nat.le_log2 (Nat.ne_of_gt nmpos)).mpr
        (Nat.le_trans (Nat.log2_self_le (Nat.ne_of_gt np)) nle)
      let k := (52 - n.log2) + (52 - m.log2)
      have enough : 52 - (n * m).log2 ≤ k := by dsimp [k]; omega
      have mant : (n <<< (52 - n.log2)) * (m <<< (52 - m.log2)) = (n * m) <<< k := by
        simp only [Nat.shiftLeft_eq, Nat.pow_add, k]
        ac_rfl
      have exponent : -((52 - n.log2 : Nat) : Int) + -((52 - m.log2 : Nat) : Int) = -(k : Int) := by
        dsimp [k]; omega
      simp only [UnpackedFloat.mul, mant, exponent]
      rw [rounded_shift (sa * sb) (n * m) k nmpos nmbound enough, signed_product]
      change Float.Model.pack (normalize Format.binary64 ((sa * sb).apply ((n * m : Nat) : Int)) 0 .positive) = _
      rw [normalize_signed (sa * sb) (n * m) 0 .positive nmpos]

private theorem extended_zero_shift (k : Nat) :
    (ExtendedMantissa.mk 0 false false >>> k) = ExtendedMantissa.mk 0 false false := by
  simpa using extended_shift_exact 0 k

private theorem round_zero (sign : Sign) (e : Int) : round Format.binary64 sign 0 e = .zero sign := by
  simp [round, roundWithAccuracy, shiftToTargetExponent, shiftToExponent, decreaseExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, extended_zero_shift,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]

private theorem signed_remainder (sa sb : Sign) (n m : Nat) :
    Int.tmod (sa.apply (n : Int)) (sb.apply (m : Int)) = sa.apply ((n % m : Nat) : Int) := by
  cases sa <;> cases sb <;> simp [Sign.apply, ← Int.ofNat_tmod]

def CanonicalRemainder (a b : Int) : Prop := Int.tmod a b = 0 → 0 ≤ a

theorem remainder_exact (a b : Int) (ha : InRange a) (hb : InRange b) (divisor : b ≠ 0)
    (canonical : CanonicalRemainder a b) :
    Float.Model.ofInt (Int.tmod a b) = Ariadne.numberRemainder (Float.Model.ofInt a) (Float.Model.ofInt b) := by
  rcases safe_cases b hb with zero | ⟨sb, m, mp, mb, rfl⟩
  · exact False.elim (divisor zero)
  · rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
    · simp only [Int.zero_tmod, Ariadne.numberRemainder, unpack_zero, unpack_ofInt_signed sb m mp mb]
    · unfold Ariadne.numberRemainder
      rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb, signed_remainder]
      let k := max (52 - n.log2) (52 - m.log2)
      have kn : 52 - n.log2 ≤ k := Nat.le_max_left _ _
      have km : 52 - m.log2 ≤ k := Nat.le_max_right _ _
      have small : min (-((52 - n.log2 : Nat) : Int)) (-((52 - m.log2 : Nat) : Int)) = -(k : Int) := by
        dsimp [k]; omega
      have aligned (x pad : Nat) (enough : pad ≤ k) :
          (x <<< pad) * 2 ^ (-(pad : Int) - -(k : Int)).toNat = x <<< k := by
        have h := congrArg Prod.fst (align_integer x pad k enough)
        simpa [decreaseExponent, Nat.shiftLeft_eq] using h
      simp only [small, aligned n _ kn, aligned m _ km]
      have rem : (n <<< k) % (m <<< k) = (n % m) <<< k := by
        simp only [Nat.shiftLeft_eq]
        simpa [Nat.mul_comm] using Nat.mul_mod_mul_left (2 ^ k) n m
      rw [rem]
      by_cases zero : n % m = 0
      · have nonneg : 0 ≤ sa.apply (n : Int) := canonical (by rw [signed_remainder, zero]; cases sa <;> rfl)
        rw [zero]
        simp only [Nat.zero_shiftLeft, round_zero]
        cases sa with
        | negative => simp [Sign.apply] at nonneg; omega
        | positive => rfl
      · have positive : 0 < n % m := by omega
        have bound : n % m < 2 ^ 53 := Nat.lt_trans (Nat.mod_lt n mp) mb
        rw [round_shift sa (n % m) k positive bound]
        change Float.Model.pack (normalize Format.binary64 (sa.apply ((n % m : Nat) : Int)) 0 .positive) = _
        rw [normalize_signed sa (n % m) 0 .positive positive]

theorem range_iff_natAbs (a : Int) : InRange a ↔ a.natAbs ≤ 9007199254740991 := by
  cases a <;> simp [InRange, limit, Int.natAbs] <;> omega

theorem tdiv_range (a b : Int) (safe : InRange a) : InRange (a.tdiv b) := by
  rw [range_iff_natAbs] at safe ⊢
  exact Nat.le_trans (Int.natAbs_tdiv_le_natAbs a b) safe

theorem fdiv_range (a b : Int) (safe : InRange a) : InRange (a.fdiv b) := by
  rw [range_iff_natAbs] at safe ⊢
  exact Nat.le_trans (Int.natAbs_fdiv_le_natAbs a b) safe

theorem remainder_range (a b : Int) (safe : InRange a) : InRange (a.tmod b) := by
  rw [range_iff_natAbs] at safe ⊢
  rw [Int.natAbs_tmod]
  exact Nat.le_trans (Nat.mod_le _ _) safe

theorem length_range (xs : List α) (length : xs.length < 2 ^ 32) : InRange (xs.length : Int) := by
  simp only [InRange, limit]
  omega

theorem isFinite_ofInt (a : Int) (safe : InRange a) : (Float.Model.ofInt a).isFinite = true := by
  rcases safe_cases a safe with rfl | ⟨sign, n, positive, bound, rfl⟩
  · kernel_rfl
  · unfold Float.Model.isFinite
    rw [unpack_ofInt_signed sign n positive bound]
    rfl

theorem toInt_ofInt (a : Int) (safe : InRange a) : (Float.Model.ofInt a).unpack.toInt 0 0 = a := by
  rcases safe_cases a safe with rfl | ⟨sign, n, positive, bound, rfl⟩
  · kernel_rfl
  · rw [unpack_ofInt_signed sign n positive bound]
    let pad := 52 - n.log2
    have first : (-(pad : Int)).toNat = 0 := by omega
    have second : (0 - -(pad : Int)).toNat = pad := by omega
    change roundToInt sign (n <<< pad) (-(pad : Int)) = _
    simp only [roundToInt, decreaseExponent, first, Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero,
      shiftToExponent, second, ExtendedMantissa.ofMantissaAndAccuracy, extended_shift_exact]

theorem trunc_ofInt (a : Int) (safe : InRange a) :
    Builtins.numberTrunc (Float.Model.ofInt a) = Float.Model.ofInt a := by
  have zero : Float.Model.ofNat 0 = Float.Model.ofInt 0 := rfl
  simp only [Builtins.numberTrunc, isFinite_ofInt a safe, Bool.not_true, Bool.false_or, zero,
    beq_ofInt a 0 safe zero_inRange, toInt_ofInt a safe]
  by_cases eq : a = 0
  · simp [eq]
  · simp [eq]

theorem floor_ofInt (a : Int) (safe : InRange a) :
    Builtins.numberFloor (Float.Model.ofInt a) = Float.Model.ofInt a := by
  have zero : Float.Model.ofNat 0 = Float.Model.ofInt 0 := rfl
  simp only [Builtins.numberFloor, isFinite_ofInt a safe, Bool.not_true, Bool.false_or, zero,
    beq_ofInt a 0 safe zero_inRange, toInt_ofInt a safe, lt_ofInt a a safe safe, Int.lt_irrefl, ↓reduceIte]
  split <;> rfl

private theorem divCore_canonical (ma mb pa pb : Nat) (ha : ma.log2 = 52) (hb : mb.log2 = 52)
    (paBound : pa ≤ 52) (pbBound : pb ≤ 52) :
    divCore Format.binary64 ma (-(pa : Int)) mb (-(pb : Int)) =
      ((ma <<< 53) / mb, -((pa + 53 - pb : Nat) : Int), accuracyOfFraction ((ma <<< 53) % mb) mb) := by
  have target : min (-(pa : Int) - -(pb : Int))
      (Format.binary64.targetExponent (totalExponent ma (-(pa : Int)) - totalExponent mb (-(pb : Int)))) =
      -((pa + 53 - pb : Nat) : Int) := by
    simp only [Format.targetExponent, totalExponent, ha, hb, Format.mantissaBits, Format.minExponent]
    omega
  have amount : (-(pa : Int) - -(pb : Int) - -((pa + 53 - pb : Nat) : Int)).toNat = 53 := by omega
  simp only [divCore, target, amount]

private theorem div_signed_exact (sa sb : Sign) (n m : Nat) (np : 0 < n) (mp : 0 < m)
    (nb : n < 2 ^ 53) (mb : m < 2 ^ 53) (divides : n % m = 0) :
    Float.Model.ofInt ((sa / sb).apply ((n / m : Nat) : Int)) =
      Float.Model.ofInt (sa.apply (n : Int)) / Float.Model.ofInt (sb.apply (m : Int)) := by
  let q := n / m
  have product : n = q * m := by simpa [q, divides, Nat.mul_comm] using (Nat.mod_add_div n m).symm
  have qp : 0 < q := by
    by_cases h : q = 0
    · simp [h] at product; omega
    · exact Nat.pos_of_ne_zero h
  have qb : q < 2 ^ 53 := Nat.lt_of_le_of_lt (Nat.div_le_self n m) nb
  have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nb; omega
  have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mp)).mpr mb; omega
  let pa := 52 - n.log2
  let pb := 52 - m.log2
  let k := pa + 53 - pb
  have paBound : pa ≤ 52 := by dsimp [pa]; omega
  have pbBound : pb ≤ 52 := by dsimp [pb]; omega
  have mabits : (n <<< pa).log2 = 52 := by rw [log2_shift n pa np]; dsimp [pa]; omega
  have mbbits : (m <<< pb).log2 = 52 := by rw [log2_shift m pb mp]; dsimp [pb]; omega
  have denpos : 0 < m <<< pb := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos mp (Nat.two_pow_pos _)
  have exponent : pa + 53 = pb + k := by dsimp [k]; omega
  have num : (n <<< pa) <<< 53 = (m <<< pb) * (q <<< k) := by
    rw [← Nat.shiftLeft_add, exponent, product]
    simp only [Nat.shiftLeft_eq, Nat.pow_add]
    ac_rfl
  have quotient : ((n <<< pa) <<< 53) / (m <<< pb) = q <<< k := by
    rw [num, Nat.mul_div_cancel_left _ denpos]
  have remainder : ((n <<< pa) <<< 53) % (m <<< pb) = 0 := by rw [num]; simp
  have lbound : n.log2 ≤ q.log2 + m.log2 + 1 := by
    have nBound : n < 2 ^ (q.log2 + m.log2 + 2) := by
      rw [product]
      have h := Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := q)) mp)
        (Nat.mul_le_mul_left (2 ^ (q.log2 + 1)) (Nat.le_of_lt (Nat.lt_log2_self (n := m))))
      rw [← Nat.pow_add] at h
      have exponents : q.log2 + 1 + (m.log2 + 1) = q.log2 + m.log2 + 2 := by omega
      simpa only [exponents] using h
    have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nBound
    omega
  have enough : 52 - q.log2 ≤ k := by dsimp [k, pa, pb]; omega
  change _ = Float.Model.pack (UnpackedFloat.div Format.binary64 _ _)
  rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
  simp only [UnpackedFloat.div]
  have core := divCore_canonical (n <<< pa) (m <<< pb) pa pb mabits mbbits paBound pbBound
  dsimp only [pa, pb] at core quotient remainder
  rw [core]
  simp only [quotient, remainder, accuracyOfFraction, ↓reduceIte]
  rw [rounded_shift (sa / sb) q k qp qb enough]
  change Float.Model.pack (normalize Format.binary64 ((sa / sb).apply (q : Int)) 0 .positive) = _
  rw [normalize_signed (sa / sb) q 0 .positive qp]

private theorem signed_quotient (sa sb : Sign) (n m : Nat) :
    Int.tdiv (sa.apply (n : Int)) (sb.apply (m : Int)) = (sa / sb).apply ((n / m : Nat) : Int) := by
  cases sa <;> cases sb <;> simp only [Sign.apply, Int.tdiv_neg, Int.neg_tdiv, Int.neg_neg] <;> rfl

theorem div_exact_of_integral (a b : Int) (ha : InRange a) (hb : InRange b)
    (divisor : b ≠ 0) (integral : a.tmod b = 0) (canonical : a = 0 → 0 ≤ b) :
    Float.Model.ofInt (a.tdiv b) = Float.Model.ofInt a / Float.Model.ofInt b := by
  rcases safe_cases b hb with zero | ⟨sb, m, mp, mb, rfl⟩
  · exact False.elim (divisor zero)
  · rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
    · have nonneg := canonical rfl
      change _ = Float.Model.pack (UnpackedFloat.div Format.binary64 (Float.Model.ofInt 0).unpack _)
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      cases sb with
      | negative => simp [Sign.apply] at nonneg; omega
      | positive => simp only [Int.zero_tdiv]; rfl
    · have divides : n % m = 0 := by
        have h := congrArg Int.natAbs integral
        cases sa <;> cases sb <;> simpa [Int.natAbs_tmod, Sign.apply] using h
      rw [signed_quotient]
      exact div_signed_exact sa sb n m np mp nb mb divides

theorem trunc_div_exact_of_integral (a b : Int) (ha : InRange a) (hb : InRange b)
    (divisor : b ≠ 0) (integral : a.tmod b = 0) (canonical : a = 0 → 0 ≤ b) :
    Builtins.numberTrunc (Float.Model.ofInt a / Float.Model.ofInt b) = Float.Model.ofInt (a.tdiv b) := by
  rw [← div_exact_of_integral a b ha hb divisor integral canonical]
  exact trunc_ofInt _ (tdiv_range a b ha)

theorem floor_div_exact_of_integral (a b : Int) (ha : InRange a) (hb : InRange b)
    (divisor : b ≠ 0) (integral : a.tmod b = 0) (canonical : a = 0 → 0 ≤ b) :
    Builtins.numberFloor (Float.Model.ofInt a / Float.Model.ofInt b) = Float.Model.ofInt (a.fdiv b) := by
  have same : a.fdiv b = a.tdiv b :=
    Int.fdiv_eq_of_eq_mul_left divisor (Int.tdiv_mul_cancel_of_tmod_eq_zero integral).symm
  rw [same, ← div_exact_of_integral a b ha hb divisor integral canonical]
  exact floor_ofInt _ (tdiv_range a b ha)

/-! Division needs more than a bound on the rounded quotient's magnitude. The
binary64 error must be smaller than the distance to either neighboring integer.
We normalize the quotient to a common power-of-two scale, prove that rounding
stays strictly inside that integer interval, and then recover truncation and
flooring from the actual Float model. -/

private theorem nearest_bounds (d : Nat) (accuracy : Accuracy) :
    d ≤ accuracy.roundToNearestEven d ∧ accuracy.roundToNearestEven d ≤ d + 1 := by
  cases accuracy with
  | exact => simp [Accuracy.roundToNearestEven]
  | inexact order => cases order <;> simp [Accuracy.roundToNearestEven] <;> omega

private theorem rounded_accuracy (d : Nat) (accuracy : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy d accuracy).roundedMantissa = accuracy.roundToNearestEven d := by
  cases accuracy with
  | exact => rfl
  | inexact order => cases order <;> rfl

private theorem unshifted_error (d r denominator : Nat) (bound : r < denominator) :
    let rounded := (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator)).roundedMantissa
    rounded * denominator ≤ d * denominator + r + denominator ∧
      d * denominator + r ≤ rounded * denominator + denominator := by
  dsimp only
  rw [rounded_accuracy]
  have bounds := nearest_bounds d (accuracyOfFraction r denominator)
  have lower := Nat.mul_le_mul_right denominator bounds.1
  have upper := Nat.mul_le_mul_right denominator bounds.2
  rw [Nat.add_mul, Nat.one_mul] at upper
  omega

private theorem shifted_error (d r denominator : Nat) (bound : r < denominator) :
    let rounded := (ExtendedMantissa.shiftRightOne
      (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator))).roundedMantissa
    (2 * rounded) * denominator ≤ d * denominator + r + denominator ∧
      d * denominator + r ≤ (2 * rounded) * denominator + denominator := by
  have parity : d % 2 = 0 ∨ d % 2 = 1 := by omega
  have halfParity : (d / 2) % 2 = 0 ∨ (d / 2) % 2 = 1 := by omega
  have scaled := congrArg (fun n => n * denominator) (Nat.mod_add_div d 2)
  simp only [Nat.add_mul, Nat.mul_assoc] at scaled
  by_cases exact : r = 0
  · subst r
    rcases parity with parity | parity <;> rcases halfParity with halfParity | halfParity
    all_goals simp [accuracyOfFraction, ExtendedMantissa.ofMantissaAndAccuracy,
      ExtendedMantissa.shiftRightOne, parity, halfParity,
      ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven,
      Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    all_goals omega
  · cases order : compare (2 * r) denominator <;> rcases parity with parity | parity
    all_goals simp [accuracyOfFraction, exact, order, ExtendedMantissa.ofMantissaAndAccuracy,
      ExtendedMantissa.shiftRightOne, parity,
      ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven,
      Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    all_goals omega

private theorem shift_add (d : Nat) (e : Int) (accuracy : Accuracy) (shift : Nat) :
    shiftToExponent d e accuracy (e + shift) =
      (ExtendedMantissa.ofMantissaAndAccuracy d accuracy >>> shift, e + shift) := by
  have amount : (e + (shift : Int) - e).toNat = shift := by omega
  simp [shiftToExponent, amount]

private theorem quotient_log (d : Nat) (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54) :
    d.log2 = 52 ∨ d.log2 = 53 := by
  have positive : d ≠ 0 := by omega
  have lower := (Nat.le_log2 positive).mpr lo
  have upper := (Nat.log2_lt positive).mpr hi
  omega

private def divisionShift (d : Nat) := d.log2 - 52
private def divisionRounded (d r denominator : Nat) :=
  ((ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator)) >>> divisionShift d).roundedMantissa

private theorem division_shift_cases (d : Nat) (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54) :
    divisionShift d = 0 ∨ divisionShift d = 1 := by
  rcases quotient_log d lo hi with h | h <;> simp [divisionShift, h]

private theorem division_target (d k : Nat) (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54)
    (kbound : k ≤ 105) :
    Format.binary64.targetExponent (totalExponent d (-(k : Int))) = -(k : Int) + divisionShift d := by
  rcases quotient_log d lo hi with bits | bits
  all_goals simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
    Format.minExponent, divisionShift, bits]
  all_goals omega

private theorem division_rounded_bounds (d r denominator : Nat) (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54) :
    2 ^ 52 ≤ divisionRounded d r denominator ∧ divisionRounded d r denominator ≤ 2 ^ 53 := by
  rcases quotient_log d lo hi with bits | bits
  · have dbound : d < 2 ^ 53 := (Nat.log2_lt (by omega)).mp (by omega)
    have h := nearest_bounds d (accuracyOfFraction r denominator)
    simp only [divisionRounded, divisionShift, bits, Nat.sub_self, HShiftRight.hShiftRight, Nat.repeat,
      rounded_accuracy]
    omega
  · have lower : 2 ^ 53 ≤ d := (Nat.le_log2 (by omega)).mp (by omega)
    have h := nearest_bounds (d / 2)
      (ExtendedMantissa.shiftRightOne (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator))).accuracy
    simp only [divisionRounded, divisionShift, bits]
    change 2 ^ 52 ≤ (ExtendedMantissa.shiftRightOne
      (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator))).roundedMantissa ∧
      (ExtendedMantissa.shiftRightOne
      (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator))).roundedMantissa ≤ 2 ^ 53
    have mantissa : (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator)).mantissa = d := by
      cases accuracyOfFraction r denominator with
      | exact => rfl
      | inexact order => cases order <;> rfl
    simp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.shiftRightOne, mantissa] at h ⊢
    omega

private theorem division_rounded_error (d r denominator : Nat) (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54)
    (bound : r < denominator) :
    divisionRounded d r denominator * 2 ^ divisionShift d * denominator ≤ d * denominator + r + denominator ∧
      d * denominator + r ≤ divisionRounded d r denominator * 2 ^ divisionShift d * denominator + denominator := by
  rcases division_shift_cases d lo hi with shift | shift
  · simpa [divisionRounded, shift, HShiftRight.hShiftRight, Nat.repeat] using unshifted_error d r denominator bound
  · simpa [divisionRounded, shift, HShiftRight.hShiftRight, Nat.repeat, Nat.mul_comm] using shifted_error d r denominator bound

private def divisionCarry (m : Nat) := if m = 2 ^ 53 then 1 else 0
private def divisionMantissa (m : Nat) := if m = 2 ^ 53 then 2 ^ 52 else m

private theorem division_mantissa_bits (m : Nat) (lo : 2 ^ 52 ≤ m) (hi : m ≤ 2 ^ 53) :
    (divisionMantissa m).log2 = 52 := by
  by_cases overflow : m = 2 ^ 53
  · simp [divisionMantissa, overflow]; decide
  · simp only [divisionMantissa, overflow, ↓reduceIte]
    exact (Nat.log2_eq_iff (by omega)).mpr ⟨lo, by omega⟩

private theorem division_mantissa_positive (m : Nat) (lo : 2 ^ 52 ≤ m) : 0 < divisionMantissa m := by
  unfold divisionMantissa
  split <;> omega

private theorem division_mantissa_scaled (m : Nat) (lo : 2 ^ 52 ≤ m) (hi : m ≤ 2 ^ 53) :
    divisionMantissa m * 2 ^ divisionCarry m = m := by
  by_cases overflow : m = 2 ^ 53
  · subst m; decide
  · simp [divisionMantissa, divisionCarry, overflow]

private theorem division_final_shift (m : Nat) (e : Int) (lo : 2 ^ 52 ≤ m) (hi : m ≤ 2 ^ 53)
    (lower : -105 ≤ e) :
    shiftToTargetExponent Format.binary64 m e .exact =
      (⟨divisionMantissa m, false, false⟩, e + divisionCarry m) := by
  have bits : m.log2 = 52 + divisionCarry m := by
    by_cases overflow : m = 2 ^ 53
    · subst m; decide
    · simp only [divisionCarry, overflow, ↓reduceIte, Nat.add_zero]
      exact (Nat.log2_eq_iff (by omega)).mpr ⟨lo, by omega⟩
  have target : Format.binary64.targetExponent (totalExponent m e) = e + divisionCarry m := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent, bits]
    have nonnegative : 0 ≤ (divisionCarry m : Int) := by omega
    omega
  unfold shiftToTargetExponent
  rw [target, shift_add]
  by_cases overflow : m = 2 ^ 53
  · subst m
    simp [divisionCarry, divisionMantissa, HShiftRight.hShiftRight, Nat.repeat,
      ExtendedMantissa.shiftRightOne, ExtendedMantissa.ofMantissaAndAccuracy]
  · simp [divisionCarry, divisionMantissa, overflow, HShiftRight.hShiftRight, Nat.repeat,
      ExtendedMantissa.ofMantissaAndAccuracy]

private theorem division_round_finite (sign : Sign) (d r denominator k : Nat)
    (lo : 2 ^ 52 ≤ d) (hi : d < 2 ^ 54) (kbound : k ≤ 105) :
    roundWithAccuracy Format.binary64 sign d (-(k : Int)) (accuracyOfFraction r denominator) =
      .finite sign (divisionMantissa (divisionRounded d r denominator))
        (-(k : Int) + divisionShift d + divisionCarry (divisionRounded d r denominator))
        (division_mantissa_positive _ (division_rounded_bounds d r denominator lo hi).1) := by
  have first : shiftToTargetExponent Format.binary64 d (-(k : Int)) (accuracyOfFraction r denominator) =
      (ExtendedMantissa.ofMantissaAndAccuracy d (accuracyOfFraction r denominator) >>> divisionShift d,
        -(k : Int) + divisionShift d) := by
    unfold shiftToTargetExponent
    rw [division_target d k lo hi kbound, shift_add]
  have lower : -105 ≤ -(k : Int) + divisionShift d := by omega
  have second := division_final_shift (divisionRounded d r denominator) (-(k : Int) + divisionShift d)
    (division_rounded_bounds d r denominator lo hi).1 (division_rounded_bounds d r denominator lo hi).2 lower
  have positive := division_mantissa_positive _ (division_rounded_bounds d r denominator lo hi).1
  unfold roundWithAccuracy
  rw [first]
  change (let (mantissa, exponent) := shiftToTargetExponent Format.binary64 (divisionRounded d r denominator) (-(k : Int) + divisionShift d) .exact;
    if h : mantissa.mantissa = 0 then UnpackedFloat.zero sign
    else .finite sign mantissa.mantissa exponent (Nat.pos_of_ne_zero h)) = _
  rw [second]
  simp [Nat.ne_of_gt positive]

/-- A one-unit rounding error at this scale cannot cross an integer boundary. -/
private theorem quotient_interval (n m scale rounded : Nat) (divisor : 0 < m)
    (nonintegral : 0 < n % m) (precision : m < scale)
    (upper : rounded * m ≤ n * scale + m) (lower : n * scale ≤ rounded * m + m) :
    (n / m) * scale < rounded ∧ rounded < (n / m + 1) * scale := by
  have remBound := Nat.mod_lt n divisor
  have equation : n * scale = (n / m) * scale * m + (n % m) * scale := by
    calc
      n * scale = (n % m + m * (n / m)) * scale := congrArg (fun x => x * scale) (Nat.mod_add_div n m).symm
      _ = _ := by rw [Nat.add_mul]; ac_rfl
  have gapLo : m < (n % m) * scale :=
    Nat.lt_of_lt_of_le precision (by simpa using Nat.mul_le_mul_right scale nonintegral)
  have gapHi : (n % m) * scale + m < m * scale := by
    have h := Nat.mul_le_mul_right scale (show n % m + 1 ≤ m by omega)
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  constructor
  · apply Nat.lt_of_not_ge
    intro fail
    have h := Nat.mul_le_mul_right m (show rounded ≤ n / m * scale by omega)
    rw [equation] at lower
    omega
  · apply Nat.lt_of_not_ge
    intro fail
    have h := Nat.mul_le_mul_right m (show (n / m + 1) * scale ≤ rounded by omega)
    simp only [Nat.add_mul, Nat.one_mul] at h
    rw [equation] at upper
    have commute : scale * m = m * scale := Nat.mul_comm ..
    omega

private theorem accuracy_scaled (r m scale : Nat) (positive : 0 < scale) :
    accuracyOfFraction (r * scale) (m * scale) = accuracyOfFraction r m := by
  simp [accuracyOfFraction, Nat.mul_eq_zero, Nat.ne_of_gt positive, Nat.compare_eq_ite_lt,
    ← Nat.mul_assoc, Nat.mul_lt_mul_right positive]

private def quotientScale (n m : Nat) := 52 - n.log2 + 53 - (52 - m.log2)

private theorem divCore_integer (n m : Nat) (np : 0 < n) (mp : 0 < m)
    (nb : n < 2 ^ 53) (mb : m < 2 ^ 53) :
    divCore Format.binary64 (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int))
      (m <<< (52 - m.log2)) (-((52 - m.log2 : Nat) : Int)) =
      ((n * 2 ^ quotientScale n m) / m, -(quotientScale n m : Int),
        accuracyOfFraction ((n * 2 ^ quotientScale n m) % m) m) := by
  have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nb; omega
  have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mp)).mpr mb; omega
  have bitsn : (n <<< (52 - n.log2)).log2 = 52 := by rw [log2_shift _ _ np]; omega
  have bitsm : (m <<< (52 - m.log2)).log2 = 52 := by rw [log2_shift _ _ mp]; omega
  rw [divCore_canonical _ _ _ _ bitsn bitsm (by omega) (by omega)]
  have exponents : 52 - n.log2 + 53 = quotientScale n m + (52 - m.log2) := by unfold quotientScale; omega
  have numerator : (n <<< (52 - n.log2)) <<< 53 =
      (n * 2 ^ quotientScale n m) * 2 ^ (52 - m.log2) := by
    rw [← Nat.shiftLeft_add, Nat.shiftLeft_eq, exponents, Nat.pow_add, Nat.mul_assoc]
  rw [numerator, Nat.shiftLeft_eq]
  simp only [Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _),
    Nat.mul_mod_mul_right, accuracy_scaled _ _ _ (Nat.two_pow_pos _)]
  rfl

private theorem quotient_precision (n m : Nat) (np : 0 < n) (mp : 0 < m)
    (nb : n < 2 ^ 53) (mb : m < 2 ^ 53) (nonintegral : 0 < n % m) :
    2 ≤ quotientScale n m ∧ quotientScale n m ≤ 105 ∧ m < 2 ^ quotientScale n m := by
  have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nb; omega
  have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mp)).mpr mb; omega
  have remainderBound := Nat.mod_lt n mp
  have mlower : 1 ≤ m.log2 := (Nat.le_log2 (Nat.ne_of_gt mp)).mpr (by omega)
  have enough : m.log2 + 1 ≤ quotientScale n m := by unfold quotientScale; omega
  refine ⟨?_, ?_, Nat.lt_of_lt_of_le (Nat.lt_log2_self) (Nat.pow_le_pow_right (by decide) enough)⟩
  all_goals unfold quotientScale; omega

private theorem quotient_digit_bounds (n m : Nat) (np : 0 < n) (mp : 0 < m)
    (nb : n < 2 ^ 53) (mb : m < 2 ^ 53) :
    2 ^ 52 ≤ (n * 2 ^ quotientScale n m) / m ∧
      (n * 2 ^ quotientScale n m) / m < 2 ^ 54 := by
  have ln : n.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt np)).mpr nb; omega
  have lm : m.log2 ≤ 52 := by have := (Nat.log2_lt (Nat.ne_of_gt mp)).mpr mb; omega
  have bitsn : (n <<< (52 - n.log2)).log2 = 52 := by rw [log2_shift _ _ np]; omega
  have bitsm : (m <<< (52 - m.log2)).log2 = 52 := by rw [log2_shift _ _ mp]; omega
  have npositive : 0 < n <<< (52 - n.log2) := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos np (Nat.two_pow_pos _)
  have mpositive : 0 < m <<< (52 - m.log2) := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos mp (Nat.two_pow_pos _)
  have nbound := (Nat.log2_eq_iff (Nat.ne_of_gt npositive)).mp bitsn
  have mbound := (Nat.log2_eq_iff (Nat.ne_of_gt mpositive)).mp bitsm
  have core := congrArg Prod.fst (divCore_integer n m np mp nb mb)
  rw [divCore_canonical _ _ _ _ bitsn bitsm (by omega) (by omega)] at core
  dsimp only at core
  rw [← core]
  constructor
  · rw [Nat.le_div_iff_mul_le mpositive, Nat.shiftLeft_eq]
    omega
  · rw [Nat.div_lt_iff_lt_mul mpositive, Nat.shiftLeft_eq]
    omega
private theorem extended_shift_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k generalizing em with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    have repeat_next (f : ExtendedMantissa → ExtendedMantissa) (j : Nat) (x : ExtendedMantissa) :
        Nat.repeat f (j + 1) x = Nat.repeat f j (f x) := by
      induction j with
      | zero => rfl
      | succ j h => change f (Nat.repeat f (j + 1) x) = f (Nat.repeat f j (f x)); rw [h]
    change (Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) em).mantissa = _
    rw [repeat_next]
    change ((ExtendedMantissa.shiftRightOne em) >>> k).mantissa = _
    rw [ih]
    simp only [ExtendedMantissa.shiftRightOne, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

private theorem roundToInt_negative_exponent (sign : Sign) (m k : Nat) :
    roundToInt sign m (-(k : Int)) = sign.apply ((m / 2 ^ k : Nat) : Int) := by
  have first : (-(k : Int)).toNat = 0 := by omega
  have second : (0 - -(k : Int)).toNat = k := by omega
  simp only [roundToInt, decreaseExponent, first, Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero,
    shiftToExponent, second, extended_shift_mantissa, ExtendedMantissa.ofMantissaAndAccuracy]

/-- The actual packed quotient remains strictly between consecutive integers. -/
private theorem rounded_division_shape (sign : Sign) (n m : Nat)
    (np : 0 < n) (mp : 0 < m) (nb : n < 2 ^ 53) (mb : m < 2 ^ 53)
    (nonintegral : 0 < n % m) :
    ∃ (mantissa h : Nat) (positive : 0 < mantissa), mantissa.log2 = 52 ∧ h ≤ 105 ∧
      (Float.Model.pack (roundWithAccuracy Format.binary64 sign
        ((n * 2 ^ quotientScale n m) / m) (-(quotientScale n m : Int))
        (accuracyOfFraction ((n * 2 ^ quotientScale n m) % m) m))).unpack =
        .finite sign mantissa (-(h : Int)) positive ∧
      (n / m) * 2 ^ h < mantissa ∧ mantissa < (n / m + 1) * 2 ^ h := by
  let k := quotientScale n m
  let d := (n * 2 ^ k) / m
  let r := (n * 2 ^ k) % m
  let u := divisionRounded d r m
  let s := divisionShift d + divisionCarry u
  let mantissa := divisionMantissa u
  have dbounds := quotient_digit_bounds n m np mp nb mb
  have precision := quotient_precision n m np mp nb mb nonintegral
  have ubounds := division_rounded_bounds d r m dbounds.1 dbounds.2
  have spos : s ≤ 2 := by
    have shift := division_shift_cases d dbounds.1 dbounds.2
    dsimp [s, divisionCarry]; split <;> omega
  have enough : s ≤ k := by omega
  have bits := division_mantissa_bits u ubounds.1 ubounds.2
  have positive := division_mantissa_positive u ubounds.1
  have scaled : mantissa * 2 ^ s = u * 2 ^ divisionShift d := by
    dsimp only [s]
    rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_right_comm, division_mantissa_scaled u ubounds.1 ubounds.2]
  have error := division_rounded_error d r m dbounds.1 dbounds.2 (Nat.mod_lt _ mp)
  have equation : d * m + r = n * 2 ^ k := by
    dsimp [d, r]; simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (n * 2 ^ k) m
  rw [equation] at error
  have interval := quotient_interval n m (2 ^ k) (u * 2 ^ divisionShift d) mp nonintegral precision.2.2 error.1 error.2
  have exponent : -(k : Int) + divisionShift d + divisionCarry u = -((k - s : Nat) : Int) := by
    dsimp [s] at enough ⊢; omega
  refine ⟨mantissa, k - s, positive, bits, by omega, ?_, ?_⟩
  · change (Float.Model.pack (roundWithAccuracy Format.binary64 sign d (-(k : Int))
      (accuracyOfFraction r m))).unpack = _
    rw [division_round_finite sign d r m k dbounds.1 dbounds.2 precision.2.1]
    change (Float.Model.pack (.finite sign mantissa (-(k : Int) + divisionShift d + divisionCarry u) positive)).unpack = _
    rw [exponent, unpack_pack_normal _ _ _ positive bits (by omega) (by omega)]
  · rw [← scaled] at interval
    have exponentNat : k = (k - s) + s := by omega
    have power : 2 ^ k = 2 ^ (k - s) * 2 ^ s := by rw [← Nat.pow_add, ← exponentNat]
    simpa only [power, ← Nat.mul_assoc, Nat.mul_lt_mul_right (Nat.two_pow_pos s)] using interval

private theorem rounded_division_toInt (sign : Sign) (n m : Nat)
    (np : 0 < n) (mp : 0 < m) (nb : n < 2 ^ 53) (mb : m < 2 ^ 53)
    (nonintegral : 0 < n % m) :
    (Float.Model.pack (roundWithAccuracy Format.binary64 sign
      ((n * 2 ^ quotientScale n m) / m) (-(quotientScale n m : Int))
      (accuracyOfFraction ((n * 2 ^ quotientScale n m) % m) m))).unpack.toInt 0 0 =
      sign.apply ((n / m : Nat) : Int) := by
  obtain ⟨mantissa, h, positive, bits, hbound, shape, lower, upper⟩ :=
    rounded_division_shape sign n m np mp nb mb nonintegral
  rw [shape]
  change roundToInt sign mantissa (-(h : Int)) = _
  rw [roundToInt_negative_exponent]
  have ratio : mantissa / 2 ^ h = n / m := by
    have lo := (Nat.le_div_iff_mul_le (Nat.two_pow_pos h)).mpr (Nat.le_of_lt lower)
    have hi := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).mpr upper
    omega
  rw [ratio]

private theorem div_signed_toInt (sa sb : Sign) (n m : Nat)
    (np : 0 < n) (mp : 0 < m) (nb : n < 2 ^ 53) (mb : m < 2 ^ 53) :
    (Float.Model.ofInt (sa.apply (n : Int)) / Float.Model.ofInt (sb.apply (m : Int))).unpack.toInt 0 0 =
      (sa / sb).apply ((n / m : Nat) : Int) := by
  by_cases integral : n % m = 0
  · rw [← div_signed_exact sa sb n m np mp nb mb integral]
    apply toInt_ofInt
    change InRange ((sa / sb).apply ((n / m : Nat) : Int))
    have bound := Nat.lt_of_le_of_lt (Nat.div_le_self n m) nb
    generalize n / m = q at *
    cases sa / sb <;> simp only [Sign.apply, InRange, limit]
    all_goals omega
  · change (Float.Model.pack (UnpackedFloat.div Format.binary64 _ _)).unpack.toInt 0 0 = _
    rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
    simp only [UnpackedFloat.div]
    rw [divCore_integer n m np mp nb mb]
    exact rounded_division_toInt (sa / sb) n m np mp nb mb (by omega)

/-- Integer conversion of a safe-integer quotient agrees with truncating integer division,
including nonintegral quotients and signed zero. -/
theorem toInt_div (a b : Int) (ha : InRange a) (hb : InRange b) (divisor : b ≠ 0) :
    (Float.Model.ofInt a / Float.Model.ofInt b).unpack.toInt 0 0 = a.tdiv b := by
  rcases safe_cases b hb with zero | ⟨sb, m, mp, mb, rfl⟩
  · exact False.elim (divisor zero)
  · rcases safe_cases a ha with rfl | ⟨sa, n, np, nb, rfl⟩
    · change (Float.Model.pack (UnpackedFloat.div Format.binary64 _ _)).unpack.toInt 0 0 = _
      rw [unpack_zero, unpack_ofInt_signed sb m mp mb]
      cases sb <;> simp only [Int.zero_tdiv, UnpackedFloat.div]
      all_goals kernel_rfl
    · rw [signed_quotient]
      exact div_signed_toInt sa sb n m np mp nb mb
private theorem div_signed_shape (sa sb : Sign) (n m : Nat)
    (np : 0 < n) (mp : 0 < m) (nb : n < 2 ^ 53) (mb : m < 2 ^ 53)
    (nonintegral : 0 < n % m) :
    ∃ (mantissa h : Nat) (positive : 0 < mantissa), mantissa.log2 = 52 ∧ h ≤ 105 ∧
      (Float.Model.ofInt (sa.apply (n : Int)) / Float.Model.ofInt (sb.apply (m : Int))).unpack =
        .finite (sa / sb) mantissa (-(h : Int)) positive ∧
      (n / m) * 2 ^ h < mantissa ∧ mantissa < (n / m + 1) * 2 ^ h := by
  change ∃ mantissa h positive, _ ∧ _ ∧
    (Float.Model.pack (UnpackedFloat.div Format.binary64 _ _)).unpack = _ ∧ _
  rw [unpack_ofInt_signed sa n np nb, unpack_ofInt_signed sb m mp mb]
  simp only [UnpackedFloat.div]
  rw [divCore_integer n m np mp nb mb]
  exact rounded_division_shape (sa / sb) n m np mp nb mb nonintegral

private theorem fraction_compare_integer (sign : Sign) (mantissa h q : Nat)
    (positive : 0 < mantissa) (bits : mantissa.log2 = 52)
    (qb : q < 2 ^ 53) (lower : q * 2 ^ h < mantissa) :
    UnpackedFloat.compare (.finite sign mantissa (-(h : Int)) positive)
      (Float.Model.ofInt (sign.apply (q : Int))).unpack =
      some (match sign with | .negative => .lt | .positive => .gt) := by
  by_cases zero : q = 0
  · subst q
    cases sign <;> simp only [Sign.apply, Int.natCast_zero, Int.neg_zero, unpack_zero, UnpackedFloat.compare]
  · have qp := Nat.pos_of_ne_zero zero
    have mbound := ((Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp bits).2
    have shiftedBound : q <<< h < 2 ^ 53 := by simpa [Nat.shiftLeft_eq] using Nat.lt_trans lower mbound
    have shiftedPositive : 0 < q <<< h := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos qp (Nat.two_pow_pos _)
    have logbound := (Nat.log2_lt (Nat.ne_of_gt shiftedPositive)).mpr shiftedBound
    rw [log2_shift q h qp] at logbound
    have enough : h ≤ 52 - q.log2 := by omega
    rw [unpack_ofInt_signed sign q qp qb]
    have order : (compare (-(h : Int)) (-((52 - q.log2 : Nat) : Int))).then
        (compare mantissa (q <<< (52 - q.log2))) = .gt := by
      by_cases same : h = 52 - q.log2
      · rw [← same, Std.ReflOrd.compare_self, Ordering.eq_then]
        exact Nat.compare_eq_gt.mpr (by simpa [Nat.shiftLeft_eq] using lower)
      · have exp : -((52 - q.log2 : Nat) : Int) < -(h : Int) := by omega
        simp [Int.compare_eq_gt.mpr exp]
    cases sign <;> simp only [UnpackedFloat.compare, order, Ordering.swap_gt]
private theorem trunc_fraction (x : Float.Model) (sign : Sign) (mantissa h q : Nat)
    (positive : 0 < mantissa)
    (shape : x.unpack = .finite sign mantissa (-(h : Int)) positive)
    (conversion : x.unpack.toInt 0 0 = sign.apply (q : Int))
    (canonical : q = 0 → sign = .positive) :
    Builtins.numberTrunc x = Float.Model.ofInt (sign.apply (q : Int)) := by
  have zero : (Float.Model.ofNat 0).unpack = .zero .positive := unpack_zero
  have nonzero : (x == Float.Model.ofNat 0) = false := by
    change (x.unpack.compare (Float.Model.ofNat 0).unpack == some .eq) = false
    rw [shape, zero]; cases sign <;> rfl
  have finite : x.isFinite = true := by rw [Float.Model.isFinite, shape]; rfl
  simp only [Builtins.numberTrunc, finite, Bool.not_true, nonzero, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, conversion]
  cases sign with
  | positive =>
    have notnegative : ¬ x < Float.Model.ofNat 0 := by
      change ¬ (x.unpack.compare (Float.Model.ofNat 0).unpack == some .lt) = true
      rw [shape, zero]; simp only [UnpackedFloat.compare]; decide
    simp [notnegative]
  | negative =>
    have nonzero : q ≠ 0 := by intro h; have := canonical h; contradiction
    simp [Sign.apply, nonzero]

private theorem floor_fraction (x : Float.Model) (sign : Sign) (mantissa h q : Nat)
    (positive : 0 < mantissa) (bits : mantissa.log2 = 52)
    (shape : x.unpack = .finite sign mantissa (-(h : Int)) positive)
    (conversion : x.unpack.toInt 0 0 = sign.apply (q : Int))
    (qb : q < 2 ^ 53) (lower : q * 2 ^ h < mantissa) :
    Builtins.numberFloor x = Float.Model.ofInt
      (match sign with | .positive => (q : Int) | .negative => -(q : Int) - 1) := by
  have zero : (Float.Model.ofNat 0).unpack = .zero .positive := unpack_zero
  have nonzero : (x == Float.Model.ofNat 0) = false := by
    change (x.unpack.compare (Float.Model.ofNat 0).unpack == some .eq) = false
    rw [shape, zero]; cases sign <;> rfl
  have finite : x.isFinite = true := by rw [Float.Model.isFinite, shape]; rfl
  have order := fraction_compare_integer sign mantissa h q positive bits qb lower
  have comparison : (x < Float.Model.ofInt (sign.apply (q : Int))) ↔ sign = .negative := by
    change ((x.unpack.compare (Float.Model.ofInt (sign.apply (q : Int))).unpack == some .lt) = true) ↔ _
    rw [shape, order]; cases sign <;> decide
  simp only [Builtins.numberFloor, finite, Bool.not_true, nonzero, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, conversion, gt_iff_lt, comparison]
  cases sign <;> simp [Sign.apply]
/-- Truncating to zero must not produce the negative-zero bit pattern. -/
def CanonicalTruncQuotient (a b : Int) : Prop := a.tdiv b = 0 → (a < 0 ↔ b < 0)

/-- Truncation after binary64 division agrees with integer truncating division,
provided its zero result has the canonical positive sign. -/
theorem trunc_div_exact (a b : Int) (ha : InRange a) (hb : InRange b)
    (divisor : b ≠ 0) (canonical : CanonicalTruncQuotient a b) :
    Builtins.numberTrunc (Float.Model.ofInt a / Float.Model.ofInt b) = Float.Model.ofInt (a.tdiv b) := by
  by_cases integral : a.tmod b = 0
  · apply trunc_div_exact_of_integral a b ha hb divisor integral
    intro zero
    subst a
    have h := canonical (by simp)
    omega
  · rcases safe_cases b hb with zero | ⟨sb, m, mp, mb, rfl⟩
    · exact False.elim (divisor zero)
    · rcases safe_cases a ha with zero | ⟨sa, n, np, nb, rfl⟩
      · simp [zero] at integral
      · have nonintegral : 0 < n % m := by
          have h : n % m ≠ 0 := by
            intro h
            apply integral
            cases sa <;> cases sb <;> simp [Sign.apply, Int.tmod_neg, Int.neg_tmod, ← Int.ofNat_tmod, h]
          omega
        obtain ⟨mantissa, h, positive, bits, hbound, shape, lower, upper⟩ :=
          div_signed_shape sa sb n m np mp nb mb nonintegral
        rw [signed_quotient]
        apply trunc_fraction _ (sa / sb) mantissa h (n / m) positive shape
          (div_signed_toInt sa sb n m np mp nb mb)
        intro zero
        have eq : (sa.apply (n : Int)).tdiv (sb.apply (m : Int)) = 0 := by
          rw [signed_quotient, zero]; cases sa / sb <;> rfl
        have same := canonical eq
        cases sa <;> cases sb <;> simp only [Sign.apply] at same ⊢ <;> try rfl
        all_goals omega

/-- Flooring a zero numerator must preserve positive zero. -/
def CanonicalFloorQuotient (a b : Int) : Prop := a = 0 → 0 ≤ b

/-- Flooring after binary64 division agrees with integer floor division. -/
theorem floor_div_exact (a b : Int) (ha : InRange a) (hb : InRange b)
    (divisor : b ≠ 0) (canonical : CanonicalFloorQuotient a b) :
    Builtins.numberFloor (Float.Model.ofInt a / Float.Model.ofInt b) = Float.Model.ofInt (a.fdiv b) := by
  by_cases integral : a.tmod b = 0
  · exact floor_div_exact_of_integral a b ha hb divisor integral canonical
  · rcases safe_cases b hb with zero | ⟨sb, m, mp, mb, rfl⟩
    · exact False.elim (divisor zero)
    · rcases safe_cases a ha with zero | ⟨sa, n, np, nb, rfl⟩
      · simp [zero] at integral
      · have nonintegral : 0 < n % m := by
          have h : n % m ≠ 0 := by
            intro h
            apply integral
            cases sa <;> cases sb <;> simp [Sign.apply, Int.tmod_neg, Int.neg_tmod, ← Int.ofNat_tmod, h]
          omega
        obtain ⟨mantissa, h, positive, bits, hbound, shape, lower, upper⟩ :=
          div_signed_shape sa sb n m np mp nb mb nonintegral
        have rounded := floor_fraction _ (sa / sb) mantissa h (n / m) positive bits shape
          (div_signed_toInt sa sb n m np mp nb mb)
          (Nat.lt_of_le_of_lt (Nat.div_le_self n m) nb) lower
        rw [rounded]
        have notDivides : ¬ (sb.apply (m : Int)) ∣ (sa.apply (n : Int)) := by
          intro h
          exact integral (Int.tmod_eq_zero_of_dvd h)
        rw [Int.fdiv_eq_tdiv, ite_eq_right notDivides, signed_quotient]
        have npositive : (0 : Int) < n := by omega
        have mpositive : (0 : Int) < m := by omega
        cases sa <;> cases sb <;> simp [Sign.apply, Nat.ne_of_gt np, Nat.ne_of_gt mp, Int.sign_eq_one_of_pos mpositive] <;> rfl

end Ariadne.Shallow.Int53

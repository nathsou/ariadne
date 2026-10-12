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
    (positive : 0 < m) (bits : m.log2 = 52) (lower : -52 ≤ e) (upper : e ≤ 0) :
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
end Ariadne.Shallow.Int53

module

public import ASDExplicitGamma.Native.GenericSourceRowsAssembly
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! The infinite-depth raw source profile uses true powers of three.  This
module separates that unbounded profile from the finite rational `E` profile
and proves the growth estimate needed by the allocated complete tail. -/
@[expose] public section

namespace ASDExplicitGamma.Native

/-- The unbounded-depth exponential shell variance. -/
noncomputable def nativeSourceExponentialVarianceCap (gamma : ℝ) (h : ℕ) : ℝ :=
  (9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * (h : ℝ) * gamma)

/-- The unbounded-depth exponential p=128 response cap. -/
noncomputable def nativeSourceExponentialFullResponseCap (gamma : ℝ) (h : ℕ) : ℝ :=
  4 * ((1009309 : ℝ) / 500000 + gamma *
    ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
      (3 : ℝ) ^ ((2 * (h : ℝ) + 4) * gamma)

/-- The unbounded-depth p=20 moment increment, with the exact source
coefficients. -/
noncomputable def nativeSourceExponentialRawIncrement (gamma : ℝ) (h : ℕ) : ℝ :=
  nativeSourceRawMomentIncrement h (nativeSourceExponentialVarianceCap gamma h)
    (nativeSourceExponentialFullResponseCap gamma h)

/-- The unbounded-depth scalar frame input, retaining the source's initial
averaged mean. -/
noncomputable def nativeSourceExponentialRawFrameInput
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) +
    nativeSourceExponentialRawIncrement gamma h

/-- The true-exponential raw frame used past the finite rational domain. -/
noncomputable def nativeSourceExponentialRawFrame
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * (h : ℝ) * gamma) *
    ((1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta h +
      8 * (1 + 1 / nativeSourceFrameEta) *
        ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2)

private noncomputable def nativeSourceExpRawLinearCoeff (h : ℕ) : ℝ :=
  (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128

private noncomputable def nativeSourceExpRawResponseCoeff : ℝ :=
  2 * nativeSourceK * nativeSourceB128 +
    (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2

/-- On the finite source domain the rational factor `E(2γh)` majorizes its
true exponential counterpart. -/
theorem native_source_E_ge_three_power (gamma : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hh : h ≤ 1334) :
    (3 : ℝ) ^ (2 * (h : ℝ) * gamma) ≤ nativeSourceE gamma h := by
  let t : ℝ := 2 * (h : ℝ) * gamma
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htBound : t ≤ 2 * 1334 * (17 / 50000 : ℝ) := by
    dsimp [t]
    calc
      2 * (h : ℝ) * gamma ≤ 2 * 1334 * gamma := by
        apply mul_le_mul_of_nonneg_right _ hgamma
        nlinarith
      _ ≤ 2 * 1334 * (17 / 50000 : ℝ) :=
        mul_le_mul_of_nonneg_left hgamma0 (by norm_num)
  have htDomain : (11 / 10 : ℝ) * t < 1 := by
    have hendpoint : (11 / 10 : ℝ) *
        (2 * 1334 * (17 / 50000 : ℝ)) < 1 := by norm_num
    nlinarith
  have hpower := Numerics.Inverse.inv_three_power_bound t ht htDomain
  have hpower' : (3 : ℝ) ^ t ≤ (1 - (11 / 10 : ℝ) * t)⁻¹ := by
    simpa only [one_div] using hpower
  have htEq : t = 2 * (h : ℝ) * gamma := rfl
  simpa [nativeSourceE, htEq, t] using hpower'

private theorem native_source_raw_moment_increment_mono
    (h : ℕ) {e e0 f f0 : ℝ}
    (he : e ≤ e0) (he0 : 0 ≤ e0)
    (hf : 0 ≤ f) (hff : f ≤ f0) :
    nativeSourceRawMomentIncrement h e f ≤
      nativeSourceRawMomentIncrement h e0 f0 := by
  have hA : 0 ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 := by
    apply mul_nonneg
    · exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (by norm_num [nativeSourceK])
    · norm_num [nativeSourceB128]
  have hB : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by
    norm_num [nativeSourceK, nativeSourceB128]
  have hC : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
    norm_num [nativeSourceM, nativeSourceQ, nativeSourceB128]
  have hbracket :
      (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          2 * nativeSourceK * nativeSourceB128 * f +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f ≤
        (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          2 * nativeSourceK * nativeSourceB128 * f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f0 := by
    calc
      _ ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          2 * nativeSourceK * nativeSourceB128 * f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f :=
        add_le_add (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hff hB)) le_rfl
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hff hC)
  have hbracketNonneg : 0 ≤
      (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
        2 * nativeSourceK * nativeSourceB128 * f +
        (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f := by
    exact add_nonneg (add_nonneg hA (mul_nonneg hB hf)) (mul_nonneg hC hf)
  unfold nativeSourceRawMomentIncrement
  calc
    _ ≤ e0 * ((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          2 * nativeSourceK * nativeSourceB128 * f +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f) :=
      mul_le_mul_of_nonneg_right he hbracketNonneg
    _ ≤ e0 * ((78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 +
          2 * nativeSourceK * nativeSourceB128 * f0 +
          (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 * f0) :=
      mul_le_mul_of_nonneg_left hbracket he0

/-- The true exponential shell variance and response profiles are bounded by
their finite rational counterparts wherever `E` is defined. -/
theorem native_source_exponential_caps_le_generic
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    nativeSourceExponentialVarianceCap gamma h ≤
        nativeSourceGenericVarianceCap gamma h ∧
      nativeSourceExponentialFullResponseCap gamma h ≤
        nativeSourceGenericFullResponseCap gamma h := by
  have hpow := native_source_E_ge_three_power gamma h hgamma hgamma0 (by omega)
  have hpowF0 := native_source_E_ge_three_power gamma (h + 2)
    hgamma hgamma0 (by omega)
  have hargF : 2 * ((h + 2 : ℕ) : ℝ) * gamma =
      (2 * (h : ℝ) + 4) * gamma := by push_cast; ring
  have hE : 0 ≤ nativeSourceE gamma h :=
    native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
  have hEF : 0 ≤ nativeSourceE gamma (h + 2) :=
    native_source_E_nonneg gamma (h + 2) hgamma hgamma0 (by omega)
  have hcoef : 0 ≤ (1009309 : ℝ) / 500000 + gamma *
      ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216) := by
    positivity
  constructor
  · unfold nativeSourceExponentialVarianceCap nativeSourceGenericVarianceCap
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · unfold nativeSourceExponentialFullResponseCap nativeSourceGenericFullResponseCap
    rw [hargF] at hpowF0
    have hpowF : (3 : ℝ) ^ ((2 * (h : ℝ) + 4) * gamma) ≤
        nativeSourceE gamma (h + 2) := hpowF0
    exact mul_le_mul_of_nonneg_left hpowF (by positivity)

/-- The finite exponential raw-frame value at its base depth is bounded by
the exact rational raw-frame cap. -/
theorem native_source_exponential_raw_frame_le_generic
    (gamma theta : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (htheta : 0 ≤ theta)
    (hh : h ≤ 1332) :
    nativeSourceExponentialRawFrame gamma theta h ≤
      nativeSourceGenericRawFrame gamma theta h := by
  have hc := native_source_exponential_caps_le_generic gamma h hgamma hgamma0 hh
  have heExp : 0 ≤ nativeSourceExponentialVarianceCap gamma h := by
    unfold nativeSourceExponentialVarianceCap
    positivity
  have hfExp : 0 ≤ nativeSourceExponentialFullResponseCap gamma h := by
    unfold nativeSourceExponentialFullResponseCap
    positivity
  have hfRat : 0 ≤ nativeSourceGenericFullResponseCap gamma h :=
    native_source_generic_full_response_cap_nonneg gamma h hgamma hgamma0 hh
  have heRat : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have hinc := native_source_raw_moment_increment_mono h hc.1
    heRat hfExp hc.2
  have hinput : nativeSourceExponentialRawFrameInput gamma theta h ≤
      nativeSourceGenericRawFrameInput gamma theta h := by
    unfold nativeSourceExponentialRawFrameInput nativeSourceGenericRawFrameInput
    exact add_le_add le_rfl hinc
  have hinputNonneg : 0 ≤ nativeSourceExponentialRawFrameInput gamma theta h := by
    unfold nativeSourceExponentialRawFrameInput nativeSourceExponentialRawIncrement
    unfold nativeSourceRawMomentIncrement
    have hK : 0 ≤ nativeSourceK := by norm_num [nativeSourceK]
    have hB128 : 0 ≤ nativeSourceB128 := by norm_num [nativeSourceB128]
    have hM : 0 ≤ nativeSourceM := by norm_num [nativeSourceM]
    have hQ : 0 ≤ nativeSourceQ := by norm_num [nativeSourceQ]
    have hframe : 0 ≤ nativeSourceAverageFactor := by
      norm_num [nativeSourceAverageFactor]
    have he : 0 ≤ nativeSourceExponentialVarianceCap gamma h := by
      unfold nativeSourceExponentialVarianceCap
      positivity
    have hf : 0 ≤ nativeSourceExponentialFullResponseCap gamma h := by
      unfold nativeSourceExponentialFullResponseCap
      positivity
    have hA : 0 ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 := by
      positivity
    have hB : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by positivity
    have hC : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
      positivity
    have htheta' : 0 ≤ (3 / 50 : ℝ) * theta := by positivity
    positivity
  have hinputRatNonneg : 0 ≤ nativeSourceGenericRawFrameInput gamma theta h :=
    le_trans hinputNonneg hinput
  have hpow := native_source_E_ge_three_power gamma h hgamma hgamma0 (by omega)
  have hE : 0 ≤ nativeSourceE gamma h :=
    native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
  have hlin : 0 ≤ 1 + nativeSourceFrameEta := by
    norm_num [nativeSourceFrameEta]
  have hquad : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
    norm_num [nativeSourceFrameEta]
  have hbracket :
      (1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta h +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 ≤
        (1 + nativeSourceFrameEta) * nativeSourceGenericRawFrameInput gamma theta h +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hinput hlin) le_rfl
  have hbracketExpNonneg : 0 ≤
      (1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta h +
        8 * (1 + 1 / nativeSourceFrameEta) *
          ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 := by
    exact add_nonneg (mul_nonneg hlin hinputNonneg)
      (mul_nonneg hquad (sq_nonneg _))
  unfold nativeSourceExponentialRawFrame nativeSourceGenericRawFrame
    nativeSourceWeakFrame
  calc
    _ ≤ nativeSourceE gamma h *
          ((1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta h +
            8 * (1 + 1 / nativeSourceFrameEta) *
              ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hpow hbracketExpNonneg
    _ ≤ nativeSourceE gamma h *
          ((1 + nativeSourceFrameEta) * nativeSourceGenericRawFrameInput gamma theta h +
            8 * (1 + 1 / nativeSourceFrameEta) *
              ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hbracket hE

private theorem native_source_exp_power_depth_add (gamma : ℝ) (H n : ℕ) :
    (3 : ℝ) ^ (2 * ((H + n : ℕ) : ℝ) * gamma) =
      (3 : ℝ) ^ (2 * (H : ℝ) * gamma) *
        ((3 : ℝ) ^ (2 * gamma)) ^ n := by
  have hcast : ((H + n : ℕ) : ℝ) = (H : ℝ) + (n : ℝ) := by
    exact_mod_cast Nat.cast_add H n
  have hexp : 2 * ((H + n : ℕ) : ℝ) * gamma =
      2 * (H : ℝ) * gamma + (2 * gamma) * (n : ℝ) := by
    rw [hcast]
    ring
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]

private theorem native_source_exp_response_power_depth_add (gamma : ℝ) (H n : ℕ) :
    (3 : ℝ) ^ ((2 * ((H + n : ℕ) : ℝ) + 4) * gamma) =
      (3 : ℝ) ^ ((2 * (H : ℝ) + 4) * gamma) *
        ((3 : ℝ) ^ (2 * gamma)) ^ n := by
  have hcast : ((H + n : ℕ) : ℝ) = (H : ℝ) + (n : ℝ) := by
    exact_mod_cast Nat.cast_add H n
  have hexp : (2 * ((H + n : ℕ) : ℝ) + 4) * gamma =
      (2 * (H : ℝ) + 4) * gamma + (2 * gamma) * (n : ℝ) := by
    rw [hcast]
    ring
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]

private theorem native_source_exp_growth_power_eq (gamma : ℝ) (n : ℕ) :
    (((3 : ℝ) ^ (2 * gamma)) ^ n) ^ 3 = ((3 : ℝ) ^ (6 * gamma)) ^ n := by
  have hbase : ((3 : ℝ) ^ (2 * gamma)) ^ 3 = (3 : ℝ) ^ (6 * gamma) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc
    (((3 : ℝ) ^ (2 * gamma)) ^ n) ^ 3 =
        ((3 : ℝ) ^ (2 * gamma)) ^ (n * 3) := by rw [← pow_mul]
    _ = ((3 : ℝ) ^ (2 * gamma)) ^ (3 * n) := by rw [Nat.mul_comm]
    _ = (((3 : ℝ) ^ (2 * gamma)) ^ 3) ^ n := by rw [pow_mul]
    _ = ((3 : ℝ) ^ (6 * gamma)) ^ n := by rw [hbase]

private theorem native_source_exp_response_coefficient_growth
    (gamma : ℝ) (H n : ℕ) (hgamma : 0 ≤ gamma) (hH : 1 ≤ H) :
    1009309 / 500000 + gamma *
        ((32474 : ℝ) * ((H + n + 1 : ℕ) : ℝ) + 11483216) ≤
      ((n + 1 : ℕ) : ℝ) *
        (1009309 / 500000 + gamma *
          ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216)) := by
  let P : ℝ := ((n + 1 : ℕ) : ℝ)
  have hP : 1 ≤ P := by dsimp [P]; exact_mod_cast (Nat.le_add_left 1 n)
  have hP_eq : P = (n : ℝ) + 1 := by dsimp [P]; push_cast; ring
  have hHcast : 1 ≤ (H : ℝ) := by exact_mod_cast hH
  have hheight : ((H + n + 1 : ℕ) : ℝ) ≤
      ((H + 1 : ℕ) : ℝ) * P := by
    have hHmul : (H : ℝ) ≤ (H : ℝ) * P :=
      calc
        (H : ℝ) = (H : ℝ) * 1 := by ring
        _ ≤ (H : ℝ) * P :=
          mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg H)
    push_cast
    calc
      (H : ℝ) + (n : ℝ) + 1 = (H : ℝ) + ((n : ℝ) + 1) := by ring
      _ ≤ (H : ℝ) * P + P :=
        add_le_add hHmul (le_of_eq hP_eq.symm)
      _ = ((H : ℝ) + 1) * P := by ring
  have hlinear :
      (32474 : ℝ) * ((H + n + 1 : ℕ) : ℝ) + 11483216 ≤
        P * ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216) := by
    have hK : 0 ≤ (11483216 : ℝ) := by norm_num
    have hconst : (11483216 : ℝ) ≤ P * 11483216 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hP) hK]
    calc
      _ ≤ (32474 : ℝ) * (((H + 1 : ℕ) : ℝ) * P) +
          P * 11483216 :=
        add_le_add (mul_le_mul_of_nonneg_left hheight (by norm_num)) hconst
      _ = P * ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216) := by ring
  have hconst : 1009309 / 500000 ≤ P * (1009309 / 500000) := by
    have hc : 0 ≤ (1009309 : ℝ) / 500000 := by norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) hc]
  calc
    _ ≤ P * (1009309 / 500000) +
        gamma * (P * ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216)) :=
      add_le_add hconst (mul_le_mul_of_nonneg_left hlinear hgamma)
    _ = _ := by dsimp [P]; ring

private theorem native_source_exp_linear_coefficient_growth
    (H n : ℕ) (hH : 1 ≤ H) :
    nativeSourceExpRawLinearCoeff (H + n) ≤
      ((n + 1 : ℕ) : ℝ) * nativeSourceExpRawLinearCoeff H := by
  have hHcast : 1 ≤ (H : ℝ) := by exact_mod_cast hH
  have hheight : ((H + n : ℕ) : ℝ) ≤
      (H : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    have hn : (n : ℝ) ≤ (H : ℝ) * (n : ℝ) := by
      have hmul : 0 ≤ ((H : ℝ) - 1) * (n : ℝ) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hmul]
    push_cast
    calc
      (H : ℝ) + (n : ℝ) ≤ (H : ℝ) + (H : ℝ) * (n : ℝ) :=
        add_le_add le_rfl hn
      _ = (H : ℝ) * ((n : ℝ) + 1) := by ring
  have hconstant : 0 ≤ 76 * nativeSourceK := by norm_num [nativeSourceK]
  have hbase : 0 ≤ nativeSourceExpRawLinearCoeff H := by
    unfold nativeSourceExpRawLinearCoeff
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg H))
        (by norm_num [nativeSourceK]))
      (by norm_num [nativeSourceB128])
  unfold nativeSourceExpRawLinearCoeff
  have hlin : 78 * ((H + n : ℕ) : ℝ) + 76 * nativeSourceK ≤
      ((n + 1 : ℕ) : ℝ) * (78 * (H : ℝ) + 76 * nativeSourceK) := by
    have hP : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 n)
    have hleft : 78 * ((H + n : ℕ) : ℝ) ≤
        78 * (H : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      nlinarith [hheight]
    have hright : 76 * nativeSourceK ≤
        ((n + 1 : ℕ) : ℝ) * (76 * nativeSourceK) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hP) hconstant]
    calc
      _ ≤ 78 * (H : ℝ) * ((n + 1 : ℕ) : ℝ) +
          ((n + 1 : ℕ) : ℝ) * (76 * nativeSourceK) := add_le_add hleft hright
      _ = _ := by ring
  have hB128 : 0 ≤ nativeSourceB128 := by norm_num [nativeSourceB128]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hlin hB128

private theorem native_source_exp_raw_increment_eq (gamma : ℝ) (h : ℕ) :
    nativeSourceExponentialRawIncrement gamma h =
      nativeSourceExponentialVarianceCap gamma h *
        (nativeSourceExpRawLinearCoeff h +
          nativeSourceExpRawResponseCoeff *
            nativeSourceExponentialFullResponseCap gamma h) := by
  unfold nativeSourceExponentialRawIncrement nativeSourceRawMomentIncrement
    nativeSourceExpRawLinearCoeff nativeSourceExpRawResponseCoeff
  ring

private theorem native_source_exp_caps_growth
    (gamma : ℝ) (H n : ℕ) (hgamma : 0 ≤ gamma) (hH : 1 ≤ H) :
    nativeSourceExponentialVarianceCap gamma (H + n) =
        nativeSourceExponentialVarianceCap gamma H *
          ((3 : ℝ) ^ (2 * gamma)) ^ n ∧
      nativeSourceExponentialFullResponseCap gamma (H + n) ≤
        ((n + 1 : ℕ) : ℝ) * ((3 : ℝ) ^ (2 * gamma)) ^ n *
          nativeSourceExponentialFullResponseCap gamma H := by
  let P : ℝ := ((n + 1 : ℕ) : ℝ)
  let g : ℝ := ((3 : ℝ) ^ (2 * gamma)) ^ n
  have hpowE := native_source_exp_power_depth_add gamma H n
  have hpowF := native_source_exp_response_power_depth_add gamma H n
  have hcoeff := native_source_exp_response_coefficient_growth gamma H n hgamma hH
  have hbaseCoeff : 0 ≤ 1009309 / 500000 + gamma *
      ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216) := by positivity
  have hpowBase : 0 ≤ (3 : ℝ) ^ ((2 * (H : ℝ) + 4) * gamma) := by positivity
  have hgammaFactor : 0 ≤ gamma := hgamma
  constructor
  · unfold nativeSourceExponentialVarianceCap
    rw [hpowE]
    ring
  · unfold nativeSourceExponentialFullResponseCap
    rw [hpowF]
    calc
      _ ≤ 4 * (((n + 1 : ℕ) : ℝ) *
          (1009309 / 500000 + gamma *
            ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216))) *
            ((3 : ℝ) ^ ((2 * (H : ℝ) + 4) * gamma) *
              ((3 : ℝ) ^ (2 * gamma)) ^ n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
          (mul_nonneg hpowBase (by positivity))
      _ = ((n + 1 : ℕ) : ℝ) * ((3 : ℝ) ^ (2 * gamma)) ^ n *
          (4 * (1009309 / 500000 + gamma *
            ((32474 : ℝ) * ((H + 1 : ℕ) : ℝ) + 11483216)) *
            (3 : ℝ) ^ ((2 * (H : ℝ) + 4) * gamma)) := by ring

private theorem native_source_exp_raw_increment_growth
    (gamma : ℝ) (H n : ℕ) (hgamma : 0 ≤ gamma) (hH : 1 ≤ H) :
    nativeSourceExponentialRawIncrement gamma (H + n) ≤
      ((n + 1 : ℕ) : ℝ) * (((3 : ℝ) ^ (2 * gamma)) ^ n) ^ 2 *
        nativeSourceExponentialRawIncrement gamma H := by
  let P : ℝ := ((n + 1 : ℕ) : ℝ)
  let g : ℝ := ((3 : ℝ) ^ (2 * gamma)) ^ n
  have hcaps := native_source_exp_caps_growth gamma H n hgamma hH
  have hP : 1 ≤ P := by dsimp [P]; exact_mod_cast (Nat.le_add_left 1 n)
  have hbaseVar : 0 ≤ nativeSourceExponentialVarianceCap gamma H := by
    unfold nativeSourceExponentialVarianceCap
    positivity
  have hbaseLin : 0 ≤ nativeSourceExpRawLinearCoeff H := by
    unfold nativeSourceExpRawLinearCoeff
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg H))
        (by norm_num [nativeSourceK]))
      (by norm_num [nativeSourceB128])
  have hD : 0 ≤ nativeSourceExpRawResponseCoeff := by
    unfold nativeSourceExpRawResponseCoeff
    norm_num [nativeSourceK, nativeSourceB128, nativeSourceM, nativeSourceQ]
  have hbaseResp : 0 ≤ nativeSourceExponentialFullResponseCap gamma H := by
    unfold nativeSourceExponentialFullResponseCap
    positivity
  have hg : 1 ≤ g := by
    dsimp [g]
    exact one_le_pow₀ (Real.one_le_rpow (by norm_num) (by positivity))
  have hPg : P ≤ P * g := by
    have hPnonneg : 0 ≤ P := le_trans (by norm_num) hP
    nlinarith [mul_nonneg hPnonneg (sub_nonneg.mpr hg)]
  have hA := native_source_exp_linear_coefficient_growth H n hH
  have hA' : nativeSourceExpRawLinearCoeff (H + n) ≤
      P * g * nativeSourceExpRawLinearCoeff H := by
    calc
      _ ≤ P * nativeSourceExpRawLinearCoeff H := by simpa [P] using hA
      _ ≤ P * g * nativeSourceExpRawLinearCoeff H := by
        exact mul_le_mul_of_nonneg_right hPg hbaseLin
  have hresponse : nativeSourceExponentialFullResponseCap gamma (H + n) ≤
      P * g * nativeSourceExponentialFullResponseCap gamma H := by
    simpa [P, g, mul_assoc] using hcaps.2
  have hbracket :
      nativeSourceExpRawLinearCoeff (H + n) +
        nativeSourceExpRawResponseCoeff *
          nativeSourceExponentialFullResponseCap gamma (H + n) ≤
      P * g * (nativeSourceExpRawLinearCoeff H +
        nativeSourceExpRawResponseCoeff *
          nativeSourceExponentialFullResponseCap gamma H) := by
    calc
      _ ≤ P * g * nativeSourceExpRawLinearCoeff H +
          nativeSourceExpRawResponseCoeff *
            (P * g * nativeSourceExponentialFullResponseCap gamma H) :=
        add_le_add hA' (mul_le_mul_of_nonneg_left hresponse hD)
      _ = _ := by ring
  have hbaseBracket : 0 ≤ nativeSourceExpRawLinearCoeff H +
      nativeSourceExpRawResponseCoeff * nativeSourceExponentialFullResponseCap gamma H :=
    add_nonneg hbaseLin (mul_nonneg hD hbaseResp)
  rw [native_source_exp_raw_increment_eq gamma (H + n), hcaps.1]
  calc
    _ ≤ nativeSourceExponentialVarianceCap gamma H *
        ((3 : ℝ) ^ (2 * gamma)) ^ n *
          (P * ((3 : ℝ) ^ (2 * gamma)) ^ n *
            (nativeSourceExpRawLinearCoeff H +
              nativeSourceExpRawResponseCoeff *
                nativeSourceExponentialFullResponseCap gamma H)) := by
      exact mul_le_mul_of_nonneg_left hbracket
        (mul_nonneg hbaseVar (by positivity))
    _ = P * (((3 : ℝ) ^ (2 * gamma)) ^ n) ^ 2 *
        nativeSourceExponentialRawIncrement gamma H := by
      rw [native_source_exp_raw_increment_eq]
      ring

private theorem native_source_exp_raw_increment_nonneg
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma) :
    0 ≤ nativeSourceExponentialRawIncrement gamma h := by
  have hvar : 0 ≤ nativeSourceExponentialVarianceCap gamma h := by
    unfold nativeSourceExponentialVarianceCap
    positivity
  have hresp : 0 ≤ nativeSourceExponentialFullResponseCap gamma h := by
    unfold nativeSourceExponentialFullResponseCap
    positivity
  rw [native_source_exp_raw_increment_eq gamma h]
  have hlin : 0 ≤ nativeSourceExpRawLinearCoeff h := by
    unfold nativeSourceExpRawLinearCoeff
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg h))
        (by norm_num [nativeSourceK]))
      (by norm_num [nativeSourceB128])
  have hcoeff : 0 ≤ nativeSourceExpRawResponseCoeff := by
    unfold nativeSourceExpRawResponseCoeff
    norm_num [nativeSourceK, nativeSourceB128, nativeSourceM, nativeSourceQ]
  exact mul_nonneg hvar (add_nonneg hlin (mul_nonneg hcoeff hresp))

/-- The true exponential raw frame satisfies the quadratic-exponential growth bound at every depth. This
unbounded-depth statement is kept separate from the finite rational `E`
profile. -/
theorem native_source_exponential_raw_frame_growth
    (gamma theta : ℝ) (H n : ℕ) (hgamma : 0 ≤ gamma)
    (htheta : 0 ≤ theta) (hH : 1 ≤ H) :
    nativeSourceExponentialRawFrame gamma theta (H + n) ≤
      nativeSourceExponentialRawFrame gamma theta H *
        ((n + 1 : ℕ) : ℝ) ^ 2 * ((3 : ℝ) ^ (6 * gamma)) ^ n := by
  let P : ℝ := ((n + 1 : ℕ) : ℝ)
  let a : ℝ := (3 : ℝ) ^ (2 * gamma)
  let g : ℝ := a ^ n
  let scale : ℝ := P ^ 2 * g ^ 2
  let inner (h : ℕ) : ℝ :=
    (1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta h +
      8 * (1 + 1 / nativeSourceFrameEta) *
        ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2
  have hP : 1 ≤ P := by dsimp [P]; exact_mod_cast (Nat.le_add_left 1 n)
  have hPnonneg : 0 ≤ P := le_trans (by norm_num) hP
  have hPcast : P = (n : ℝ) + 1 := by dsimp [P]; push_cast; ring
  have ha : 1 ≤ a := by
    dsimp [a]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hg : 1 ≤ g := by dsimp [g]; exact one_le_pow₀ ha
  have hP2 : P ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 1)]
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hscale : 1 ≤ scale := by
    dsimp [scale]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P ^ 2 * g ^ 2 :=
        mul_le_mul (one_le_pow₀ hP) hg2 (by norm_num) (sq_nonneg P)
  have hinputScale : P * g ^ 2 ≤ scale := by
    dsimp [scale]
    exact mul_le_mul_of_nonneg_right hP2 (sq_nonneg g)
  have hinputFactor : 1 ≤ P * g ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P * g ^ 2 :=
        mul_le_mul hP hg2
          (by norm_num) hPnonneg
  have hPgScale : P * g ≤ scale := by
    have hgSq : g ≤ g ^ 2 := by
      calc
        g = 1 * g := by ring
        _ ≤ g * g := mul_le_mul_of_nonneg_right hg (by positivity)
        _ = g ^ 2 := by ring
    calc
      P * g ≤ P ^ 2 * g := mul_le_mul_of_nonneg_right hP2 (by positivity)
      _ ≤ P ^ 2 * g ^ 2 := mul_le_mul_of_nonneg_left hgSq (by positivity)
  have hpowShift := native_source_exp_power_depth_add gamma H n
  have hinc := native_source_exp_raw_increment_growth gamma H n hgamma hH
  have hconst : 0 ≤ nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) := by
    have havg : 0 ≤ nativeSourceAverageFactor := by
      norm_num [nativeSourceAverageFactor]
    exact mul_nonneg havg (mul_nonneg (by norm_num) htheta)
  have hincBase : 0 ≤ nativeSourceExponentialRawIncrement gamma H :=
    native_source_exp_raw_increment_nonneg gamma H hgamma
  have hinput : nativeSourceExponentialRawFrameInput gamma theta (H + n) ≤
      P * g ^ 2 * nativeSourceExponentialRawFrameInput gamma theta H := by
    unfold nativeSourceExponentialRawFrameInput
    have hconstScale :
        nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) ≤
          P * g ^ 2 * (nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta)) := by
      calc
        _ = 1 * (nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hinputFactor hconst
    calc
      _ ≤ P * g ^ 2 * (nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta)) +
          P * g ^ 2 * nativeSourceExponentialRawIncrement gamma H :=
        add_le_add hconstScale hinc
      _ = P * g ^ 2 * (nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) +
          nativeSourceExponentialRawIncrement gamma H) := by ring
      _ = P * g ^ 2 * nativeSourceExponentialRawFrameInput gamma theta H := rfl
  have hinputBase : 0 ≤ nativeSourceExponentialRawFrameInput gamma theta H := by
    unfold nativeSourceExponentialRawFrameInput
    exact add_nonneg hconst hincBase
  have hdepth : ((H + n : ℕ) : ℝ) ≤ (H : ℝ) * P := by
    have hHreal : 1 ≤ (H : ℝ) := by exact_mod_cast hH
    have hn : (n : ℝ) ≤ (H : ℝ) * (n : ℝ) := by
      have hmul : 0 ≤ ((H : ℝ) - 1) * (n : ℝ) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg n)
      nlinarith [hmul]
    rw [hPcast]
    push_cast
    calc
      (H : ℝ) + (n : ℝ) ≤ (H : ℝ) + (H : ℝ) * (n : ℝ) :=
        add_le_add le_rfl hn
      _ = (H : ℝ) * ((n : ℝ) + 1) := by ring
  have hlinearCoeff : 0 ≤ 1 + nativeSourceFrameEta := by
    norm_num [nativeSourceFrameEta]
  have hquadCoeff : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
    norm_num [nativeSourceFrameEta]
  let tH : ℝ := (11 / 10 : ℝ) * gamma * (H : ℝ)
  let tn : ℝ := (11 / 10 : ℝ) * gamma * ((H + n : ℕ) : ℝ)
  have htH : 0 ≤ tH := by dsimp [tH]; positivity
  have htn : 0 ≤ tn := by dsimp [tn]; positivity
  have htnBound : tn ≤ P * tH := by
    dsimp [tn, tH]
    calc
      _ ≤ (11 / 10 : ℝ) * gamma * ((H : ℝ) * P) :=
        mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = P * ((11 / 10 : ℝ) * gamma * (H : ℝ)) := by ring
  have htnSq : tn ^ 2 ≤ P ^ 2 * tH ^ 2 := by
    calc
      tn ^ 2 = tn * tn := by ring
      _ ≤ (P * tH) * tn :=
        mul_le_mul_of_nonneg_right htnBound htn
      _ ≤ (P * tH) * (P * tH) :=
        mul_le_mul_of_nonneg_left htnBound (by positivity)
      _ = P ^ 2 * tH ^ 2 := by ring
  have hquad :
      8 * (1 + 1 / nativeSourceFrameEta) * tn ^ 2 ≤
        scale * (8 * (1 + 1 / nativeSourceFrameEta) * tH ^ 2) := by
    have hscaleQuad : P ^ 2 ≤ scale := by
      have hfactor : 1 ≤ g ^ 2 := hg2
      dsimp [scale]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor (sq_nonneg P)
    calc
      _ ≤ 8 * (1 + 1 / nativeSourceFrameEta) * (P ^ 2 * tH ^ 2) :=
        mul_le_mul_of_nonneg_left htnSq hquadCoeff
      _ = P ^ 2 * (8 * (1 + 1 / nativeSourceFrameEta) * tH ^ 2) := by ring
      _ ≤ scale * (8 * (1 + 1 / nativeSourceFrameEta) * tH ^ 2) :=
        mul_le_mul_of_nonneg_right hscaleQuad (by positivity)
  have hlinear :
      (1 + nativeSourceFrameEta) * nativeSourceExponentialRawFrameInput gamma theta (H + n) ≤
        scale * ((1 + nativeSourceFrameEta) *
          nativeSourceExponentialRawFrameInput gamma theta H) := by
    calc
      _ ≤ (1 + nativeSourceFrameEta) *
          (P * g ^ 2 * nativeSourceExponentialRawFrameInput gamma theta H) :=
        mul_le_mul_of_nonneg_left hinput hlinearCoeff
      _ ≤ scale * ((1 + nativeSourceFrameEta) *
          nativeSourceExponentialRawFrameInput gamma theta H) := by
        calc
          _ = (P * g ^ 2) *
              ((1 + nativeSourceFrameEta) *
                nativeSourceExponentialRawFrameInput gamma theta H) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hinputScale
            (mul_nonneg hlinearCoeff hinputBase)
  have hinner : inner (H + n) ≤ scale * inner H := by
    dsimp [inner]
    change (1 + nativeSourceFrameEta) *
          nativeSourceExponentialRawFrameInput gamma theta (H + n) +
          8 * (1 + 1 / nativeSourceFrameEta) * tn ^ 2 ≤
        scale * ((1 + nativeSourceFrameEta) *
          nativeSourceExponentialRawFrameInput gamma theta H +
          8 * (1 + 1 / nativeSourceFrameEta) * tH ^ 2)
    calc
      _ ≤ scale * ((1 + nativeSourceFrameEta) *
          nativeSourceExponentialRawFrameInput gamma theta H) +
          scale * (8 * (1 + 1 / nativeSourceFrameEta) * tH ^ 2) :=
        add_le_add hlinear hquad
      _ = _ := by ring
  have hinnerBase : 0 ≤ inner H := by
    dsimp [inner]
    exact add_nonneg (mul_nonneg hlinearCoeff hinputBase)
      (mul_nonneg hquadCoeff (sq_nonneg tH))
  have hframeBound :
      nativeSourceExponentialRawFrame gamma theta (H + n) ≤
        nativeSourceExponentialRawFrame gamma theta H * scale * g := by
    change (3 : ℝ) ^ (2 * ((H + n : ℕ) : ℝ) * gamma) * inner (H + n) ≤
      (3 : ℝ) ^ (2 * (H : ℝ) * gamma) * inner H * scale * g
    rw [hpowShift]
    calc
      _ ≤ ((3 : ℝ) ^ (2 * (H : ℝ) * gamma) * g) * (scale * inner H) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = nativeSourceExponentialRawFrame gamma theta H * scale * g := by
        simp only [nativeSourceExponentialRawFrame, inner]
        ring
  have hgrowthPower := native_source_exp_growth_power_eq gamma n
  calc
    _ ≤ nativeSourceExponentialRawFrame gamma theta H * scale * g := hframeBound
    _ = nativeSourceExponentialRawFrame gamma theta H * P ^ 2 * g ^ 3 := by
      dsimp [scale]
      ring
    _ = nativeSourceExponentialRawFrame gamma theta H * P ^ 2 *
        ((3 : ℝ) ^ (6 * gamma)) ^ n := by rw [hgrowthPower]
    _ = nativeSourceExponentialRawFrame gamma theta H *
        ((n + 1 : ℕ) : ℝ) ^ 2 * ((3 : ℝ) ^ (6 * gamma)) ^ n := by
      dsimp [P]

private theorem native_source_exponential_raw_frame_nonneg
    (gamma theta : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (htheta : 0 ≤ theta) :
    0 ≤ nativeSourceExponentialRawFrame gamma theta h := by
  have hconst : 0 ≤ nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) := by
    have havg : 0 ≤ nativeSourceAverageFactor := by
      norm_num [nativeSourceAverageFactor]
    exact mul_nonneg havg (mul_nonneg (by norm_num) htheta)
  have hinput : 0 ≤ nativeSourceExponentialRawFrameInput gamma theta h := by
    unfold nativeSourceExponentialRawFrameInput
    exact add_nonneg hconst
      (native_source_exp_raw_increment_nonneg gamma h hgamma)
  have hlinear : 0 ≤ 1 + nativeSourceFrameEta := by
    norm_num [nativeSourceFrameEta]
  have hquad : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
    norm_num [nativeSourceFrameEta]
  unfold nativeSourceExponentialRawFrame
  exact mul_nonneg (by positivity)
    (add_nonneg (mul_nonneg hlinear hinput)
      (mul_nonneg hquad (sq_nonneg _)))

/-- The true infinite source tail at offset `r` is bounded by the exact
allocation based on the finite rational frame at depth `9+r`. -/
theorem native_source_generic_raw_tail_le_charge
    (gamma theta : ℝ) (r N : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (htheta : 0 ≤ theta) (hr : r ≤ 5) :
    nativeSourceRawWeightedTail (nativeSourceHistoryWeight gamma) (9 + r) N
        (nativeSourceExponentialRawFrame gamma theta) ≤
      nativeSourceGenericTailCharge gamma theta r N := by
  let H : ℕ := 9 + r
  let q : ℝ := nativeSourceHistoryWeight gamma
  let growth : ℝ := (3 : ℝ) ^ (6 * gamma)
  have hHone : 1 ≤ H := by dsimp [H]; omega
  have hHfinite : H ≤ 1332 := by dsimp [H]; omega
  have hq := native_source_history_weight_endpoint_and_ratio gamma hgamma hgamma0
  have hqNonneg : 0 ≤ q := by simpa [q] using hq.1
  have hratio : q * growth ≤ 9 / 10 := by simpa [q, growth] using hq.2.2
  have hgrowth : 0 ≤ growth := by positivity
  have hbaseNonneg : 0 ≤ nativeSourceExponentialRawFrame gamma theta H :=
    native_source_exponential_raw_frame_nonneg gamma theta H hgamma htheta
  have hframeNonneg : ∀ j, 0 ≤ nativeSourceExponentialRawFrame gamma theta (H + j) :=
    fun j => native_source_exponential_raw_frame_nonneg gamma theta (H + j) hgamma htheta
  have hframe : ∀ j, nativeSourceExponentialRawFrame gamma theta (H + j) ≤
      nativeSourceExponentialRawFrame gamma theta H *
        ((j + 1 : ℕ) : ℝ) ^ 2 * growth ^ j := by
    intro j
    simpa [growth, mul_assoc] using
      native_source_exponential_raw_frame_growth gamma theta H j hgamma htheta hHone
  have htail := native_source_raw_weighted_tail_le q growth H N
    (nativeSourceExponentialRawFrame gamma theta) hqNonneg hgrowth hratio
    hbaseNonneg hframeNonneg hframe
  have hbaseBridge := native_source_exponential_raw_frame_le_generic
    gamma theta H hgamma hgamma0 htheta hHfinite
  have hfactor : 0 ≤ nativeSourceGenericTailFactor N := by
    unfold nativeSourceGenericTailFactor
    positivity
  have htailFactorized :
      nativeSourceRawWeightedTail q H N (nativeSourceExponentialRawFrame gamma theta) ≤
        nativeSourceExponentialRawFrame gamma theta H *
          nativeSourceGenericTailFactor N := by
    calc
      _ ≤ nativeSourceExponentialRawFrame gamma theta H *
          (((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
            (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)) := by
        simpa [nativeSourceRawWeightedTail, q, H, mul_assoc] using htail
      _ = _ := by
        unfold nativeSourceGenericTailFactor
        ring
  unfold nativeSourceGenericTailCharge
  calc
    _ ≤ nativeSourceExponentialRawFrame gamma theta H *
        nativeSourceGenericTailFactor N := htailFactorized
    _ ≤ nativeSourceGenericRawFrame gamma theta H *
        nativeSourceGenericTailFactor N :=
      mul_le_mul_of_nonneg_right hbaseBridge hfactor
    _ = nativeSourceGenericRawFrame gamma theta (9 + r) *
        nativeSourceGenericTailFactor N := by rfl

/-- The completed finite generic mean row plus its rational allocation
dominates the corresponding unbounded true-exponential mean tail. -/
theorem native_source_generic_complete_mean_row_covers_exponential_tail
    (gamma theta : ℝ) (r N : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (htheta : 0 ≤ theta) (hr : r ≤ 5) (hN : N ≤ 1285) :
    nativeSourceFiniteWeightedRow (nativeSourceHistoryWeight gamma)
        (fun j => nativeSourceGenericMeanProfile gamma theta (9 + r + j)) N +
      nativeSourceRawWeightedTail (nativeSourceHistoryWeight gamma) (9 + r) N
        (nativeSourceExponentialRawFrame gamma theta) ≤
    nativeSourceGenericCompleteMeanRow gamma theta r N := by
  have _hdepth : 9 + r + N ≤ 1299 := by omega
  have htail := native_source_generic_raw_tail_le_charge
    gamma theta r N hgamma hgamma0 htheta hr
  unfold nativeSourceGenericCompleteMeanRow nativeSourceCompleteWeightedRow
  simpa [add_comm] using add_le_add_right htail
    (nativeSourceFiniteWeightedRow (nativeSourceHistoryWeight gamma)
      (fun j => nativeSourceGenericMeanProfile gamma theta (9 + r + j)) N)

/-- The completed finite generic weak-inverse row plus its rational
allocation dominates the corresponding unbounded true-exponential tail. -/
theorem native_source_generic_complete_weak_row_covers_exponential_tail
    (gamma theta : ℝ) (r N : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (htheta : 0 ≤ theta) (hr : r ≤ 5) (hN : N ≤ 1285) :
    nativeSourceFiniteWeightedRow (nativeSourceHistoryWeight gamma)
        (fun j => nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j)) N +
      nativeSourceRawWeightedTail (nativeSourceHistoryWeight gamma) (9 + r) N
        (nativeSourceExponentialRawFrame gamma theta) ≤
    nativeSourceGenericCompleteWeakRow gamma theta r N := by
  have _hdepth : 9 + r + N ≤ 1299 := by omega
  have htail := native_source_generic_raw_tail_le_charge
    gamma theta r N hgamma hgamma0 htheta hr
  unfold nativeSourceGenericCompleteWeakRow nativeSourceCompleteWeightedRow
  simpa [add_comm] using add_le_add_right htail
    (nativeSourceFiniteWeightedRow (nativeSourceHistoryWeight gamma)
      (fun j => nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j)) N)

end ASDExplicitGamma.Native

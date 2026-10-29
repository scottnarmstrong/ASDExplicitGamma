module

public import ASDExplicitGamma.Native.ReturnsTerms
public import ASDExplicitGamma.Native.ReturnsHistory
public import ASDExplicitGamma.Native.ReturnsFrameTheta
public import ASDExplicitGamma.Native.HeatStepNodeThetaFinal

/-! NA-RETURNS at smaller gamma: the theta-scaled raw OLD envelope and the individual terms of the
native histories. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

/-- The exponential raw frame input is below the rational OLD raw envelope at the endpoint. -/
theorem nativeReturns_rawInput_theta_le (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    nativeSourceExponentialRawFrameInput M.gamma (theta M) g ≤
      theta M * ((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hz
  have hγ0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hγz : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hz
  have hγθ : M.gamma = theta M * (17 / 50000) := by
    unfold theta gammaZero; field_simp
  have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg
  have hinc := heat_old_raw_increment_le g
  have hpow3 : (3 : ℝ) ^ (2 * (g : ℝ) * M.gamma) ≤ (3 : ℝ) ^ (2 * (g : ℝ) * (17 / 50000)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hvar : nativeSourceExponentialVarianceCap M.gamma g ≤
      theta M * (((nativeRaw g).2.1 : ℚ) : ℝ) := by
    have hE := nativeReturns_three_pow_le_E (2 * (g : ℝ) * (17 / 50000)) (by positivity)
      (by nlinarith)
    simp only [nativeRaw, nativeE, nativeGamma]
    unfold nativeSourceExponentialVarianceCap
    push_cast
    have h0 : (0 : ℝ) ≤ 9 / 2 * (17 / 50000 : ℝ) := by norm_num
    calc (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * (g : ℝ) * M.gamma)
        = theta M * ((9 / 2 : ℝ) * (17 / 50000) * (3 : ℝ) ^ (2 * (g : ℝ) * M.gamma)) := by
          rw [hγθ]; ring
      _ ≤ theta M * ((9 / 2 : ℝ) * (17 / 50000) * (3 : ℝ) ^ (2 * (g : ℝ) * (17 / 50000))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow3 h0) hτ0.le
      _ ≤ theta M * ((9 / 2 : ℝ) * (17 / 50000) *
          (1 - (11 / 10 : ℝ) * (2 * (g : ℝ) * (17 / 50000)))⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE h0) hτ0.le
      _ = _ := by
          congr 1
          field_simp
  have hfull : nativeSourceExponentialFullResponseCap M.gamma g ≤ (((nativeRaw g).1 : ℚ) : ℝ) := by
    have hx0 : (0 : ℝ) ≤ (2 * (g : ℝ) + 4) * (17 / 50000) := by positivity
    have hE := nativeReturns_three_pow_le_E ((2 * (g : ℝ) + 4) * (17 / 50000)) hx0
      (by nlinarith)
    have hup := nativeUp_ge (4 * ((1009309 / 500000) + nativeGamma * (32474 * ((g : ℚ) + 1) + 11483216)) *
      nativeE ((2 * (g : ℚ) + 4) * nativeGamma))
    have hupR := (Rat.cast_le (K := ℝ)).2 hup
    refine le_trans ?_ hupR
    unfold nativeSourceExponentialFullResponseCap
    simp only [nativeE, nativeGamma]
    push_cast
    have hpow4 : (3 : ℝ) ^ ((2 * (g : ℝ) + 4) * M.gamma) ≤
        (3 : ℝ) ^ ((2 * (g : ℝ) + 4) * (17 / 50000)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h0 : (0 : ℝ) ≤ 4 * (1009309 / 500000 + M.gamma * (32474 * ((g : ℝ) + 1) + 11483216)) := by
      positivity
    have h1 : 4 * (1009309 / 500000 + M.gamma * (32474 * ((g : ℝ) + 1) + 11483216)) ≤
        4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) := by
      nlinarith
    have h2 : (0 : ℝ) ≤ 4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) := by
      positivity
    calc _ ≤ 4 * (1009309 / 500000 + M.gamma * (32474 * ((g : ℝ) + 1) + 11483216)) *
          (3 : ℝ) ^ ((2 * (g : ℝ) + 4) * (17 / 50000)) := by
          have := mul_le_mul_of_nonneg_left hpow4 h0
          simpa [Nat.cast_add, Nat.cast_one] using this
      _ ≤ 4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) *
          (1 - (11 / 10 : ℝ) * ((2 * (g : ℝ) + 4) * (17 / 50000)))⁻¹ := by
          have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 * (g : ℝ) + 4) * (17 / 50000)) := by positivity
          calc _ ≤ 4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) *
                (3 : ℝ) ^ ((2 * (g : ℝ) + 4) * (17 / 50000)) :=
                mul_le_mul_of_nonneg_right h1 hpos
            _ ≤ _ := mul_le_mul_of_nonneg_left hE h2
      _ = _ := by
        field_simp
  have hmono := nativeReturns_rawIncrement_mono g
    (show nativeSourceExponentialVarianceCap M.gamma g ≤ theta M * (((nativeRaw g).2.1 : ℚ) : ℝ) from hvar)
    hfull (by unfold nativeSourceExponentialVarianceCap; positivity)
    (by unfold nativeSourceExponentialFullResponseCap; positivity)
  have hscale : nativeSourceRawMomentIncrement g (theta M * (((nativeRaw g).2.1 : ℚ) : ℝ))
      (((nativeRaw g).1 : ℚ) : ℝ) = theta M * nativeSourceRawMomentIncrement g
        (((nativeRaw g).2.1 : ℚ) : ℝ) (((nativeRaw g).1 : ℚ) : ℝ) := by
    unfold nativeSourceRawMomentIncrement; ring
  have hincr : nativeSourceExponentialRawIncrement M.gamma g ≤
      theta M * (((nativeRaw g).2.2 : ℚ) : ℝ) := by
    have h1 : nativeSourceExponentialRawIncrement M.gamma g ≤
        nativeSourceRawMomentIncrement g (theta M * (((nativeRaw g).2.1 : ℚ) : ℝ))
          (((nativeRaw g).1 : ℚ) : ℝ) := hmono
    rw [hscale] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hinc hτ0.le)
  unfold nativeSourceExponentialRawFrameInput
  push_cast
  have : nativeSourceAverageFactor = (nativeAvg : ℝ) := by
    norm_num [nativeSourceAverageFactor, nativeAvg, nativeRoot]
  have hA : (nativeA : ℝ) = 3 / 50 := by norm_num [nativeA]
  rw [this, hA]
  linarith


/-- The exponential raw frame is below `θ` times the rational raw frame of the numerics. -/
theorem nativeReturns_rawExp_theta_le_rat (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    nativeSourceExponentialRawFrame M.gamma (theta M) g ≤
      theta M * ((nativeSourceRawFrame g : ℚ) : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hz
  have hγ0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hγz : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hz
  have hγθ : M.gamma = theta M * (17 / 50000) := by
    unfold theta gammaZero; field_simp
  have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg
  have hin := nativeReturns_rawInput_theta_le M hz g hg
  have hin0 : 0 ≤ nativeSourceExponentialRawFrameInput M.gamma (theta M) g := by
    dsimp only [nativeSourceExponentialRawFrameInput, nativeSourceExponentialRawIncrement,
      nativeSourceExponentialVarianceCap, nativeSourceExponentialFullResponseCap,
      nativeSourceAverageFactor, nativeSourceRawMomentIncrement, nativeSourceK, nativeSourceM,
      nativeSourceQ, nativeSourceB128]
    have := hγ0.le
    positivity
  have hpow3 : (3 : ℝ) ^ (2 * (g : ℝ) * M.gamma) ≤ (3 : ℝ) ^ (2 * (g : ℝ) * (17 / 50000)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hE := nativeReturns_three_pow_le_E (2 * (g : ℝ) * (17 / 50000)) (by positivity)
    (by nlinarith)
  have hEq : (1 - (11 / 10 : ℝ) * (2 * (g : ℝ) * (17 / 50000)))⁻¹ =
      (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) := by
    norm_num [nativeE, nativeGamma]; ring_nf
  rw [hEq] at hE
  have hE1 : (3 : ℝ) ^ (2 * (g : ℝ) * M.gamma) ≤ (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) :=
    hpow3.trans hE
  unfold nativeSourceExponentialRawFrame nativeSourceRawFrame
  have hη : nativeSourceFrameEta = 1 / 1000 := rfl
  rw [hη]
  push_cast
  have hE0 : (0 : ℝ) ≤ (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) := by
    norm_num [nativeE, nativeGamma]
    have : (11 / 10 : ℝ) * (2 * (17 / 50000) * (g : ℝ)) < 1 := by nlinarith
    nlinarith
  have hsec : 8 * (1 + 1 / ((1 : ℝ) / 1000)) * ((11 / 10 : ℝ) * M.gamma * (g : ℝ)) ^ 2 ≤
      theta M * (8 * (1 + 1000) * ((11 / 10 : ℝ) * (nativeGamma : ℝ) * (g : ℝ)) ^ 2) := by
    rw [hγθ]
    norm_num [nativeGamma]
    have h2 : theta M ^ 2 ≤ theta M := by nlinarith
    have h3 : 0 ≤ (g : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 h3]
  have hin' : nativeSourceExponentialRawFrameInput M.gamma (theta M) g ≤
      theta M * ((nativeAvg : ℝ) * (nativeA : ℝ) + ((nativeRaw g).2.2 : ℝ)) := by
    simpa using hin
  have hbracket : (1 + 1 / 1000 : ℝ) * nativeSourceExponentialRawFrameInput M.gamma (theta M) g +
      8 * (1 + 1 / ((1 : ℝ) / 1000)) * ((11 / 10 : ℝ) * M.gamma * (g : ℝ)) ^ 2 ≤
      theta M * ((1 + 1 / 1000 : ℝ) * ((nativeAvg : ℝ) * (nativeA : ℝ) + ((nativeRaw g).2.2 : ℝ)) +
        8 * (1 + 1000) * ((11 / 10 : ℝ) * (nativeGamma : ℝ) * (g : ℝ)) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hin' (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000)
    nlinarith [this, hsec]
  have hbr0 : 0 ≤ (1 + 1 / 1000 : ℝ) * nativeSourceExponentialRawFrameInput M.gamma (theta M) g +
      8 * (1 + 1 / ((1 : ℝ) / 1000)) * ((11 / 10 : ℝ) * M.gamma * (g : ℝ)) ^ 2 := by
    have := hγ0.le
    positivity
  calc _ ≤ (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) *
        ((1 + 1 / 1000 : ℝ) * nativeSourceExponentialRawFrameInput M.gamma (theta M) g +
          8 * (1 + 1 / ((1 : ℝ) / 1000)) * ((11 / 10 : ℝ) * M.gamma * (g : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hE1 hbr0
    _ ≤ (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) *
        (theta M * ((1 + 1 / 1000 : ℝ) * ((nativeAvg : ℝ) * (nativeA : ℝ) + ((nativeRaw g).2.2 : ℝ)) +
          8 * (1 + 1000) * ((11 / 10 : ℝ) * (nativeGamma : ℝ) * (g : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbracket hE0
    _ = _ := by ring

/-- The rational OLD raw envelope is nonnegative on the frame domain. -/
theorem nativeReturns_raw_entry_nonneg_theta (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    (0 : ℝ) ≤ ((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hz
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have h0 : 0 ≤ nativeSourceExponentialRawFrameInput M.gamma (theta M) g := by
    dsimp only [nativeSourceExponentialRawFrameInput, nativeSourceExponentialRawIncrement,
      nativeSourceExponentialVarianceCap, nativeSourceExponentialFullResponseCap,
      nativeSourceAverageFactor, nativeSourceRawMomentIncrement, nativeSourceK, nativeSourceM,
      nativeSourceQ, nativeSourceB128]
    positivity
  have := nativeReturns_rawInput_theta_le M hz g hg
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_pos_of_neg hτ0 hneg
  linarith

end ASDExplicitGamma.Native

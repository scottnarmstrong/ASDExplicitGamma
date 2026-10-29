module

public import ASDExplicitGamma.Native.OldSignedQ1MultiplierCaps
public import ASDExplicitGamma.Native.OldSignedFlatOscillationCaps

/-! Complete actual flat oscillations fit the exact q1 endpoint profiles. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Squaring the physical covariance-root bound keeps the complete gradient trace. -/
theorem old_signed_q1_scaled_gradient_energy
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    (cubeScaleFactor (originCube 2 n)/3^5)^2*mainFlatSigmaSq b L≤
      theta M*(nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)) := by
  intro b L
  have hr : 0≤cubeScaleFactor (originCube 2 n)/3^5 :=
    div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have hs : 0≤ mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hS : 0≤nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5) :=
    mul_nonneg (mul_nonneg old_signed_q1_setup_variance_nonneg (by norm_num)) (by norm_num)
  have hh : ((cubeScaleFactor (originCube 2 n)/3^5)*Real.sqrt (mainFlatSigmaSq b L))^2≤
      (Real.sqrt (theta M)*Real.sqrt (nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)))^2 :=
    pow_le_pow_left₀ (mul_nonneg hr (Real.sqrt_nonneg _))
    (old_signed_q1_scaled_gradient_root M h hg n hstate) 2
  simpa only [mul_pow,Real.sq_sqrt hs,Real.sq_sqrt (cold_theta_pos M).le,Real.sq_sqrt hS] using hh

/-- The plus whole-partition oscillation is paid by the SAME certified
plus field, with its full theta factor. -/
theorem old_signed_q1_scaled_plus_oscillation
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let Q := originCube 2 n
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L true^2)≤
      theta M*(nativeSetupQ1001FieldsR.getD 4 0)^2 := by
  intro Q b L
  let r := cubeScaleFactor Q/3^5
  let S := nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)
  have hs : 0≤S := mul_nonneg (mul_nonneg old_signed_q1_setup_variance_nonneg (by norm_num)) (by norm_num)
  have hc : planarC0^2≤(11/25:ℝ)^2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) old_signed_q1_planarC0_le 2
  have hgrad : r^2*mainFlatSigmaSq b L≤theta M*S :=
    old_signed_q1_scaled_gradient_energy M h hg n hstate
  have hSigma : 0≤ mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hprod := mul_le_mul hc hgrad (mul_nonneg (sq_nonneg r) hSigma) (sq_nonneg (11/25:ℝ))
  have hh := mul_le_mul_of_nonneg_left hprod (sq_nonneg (1+Real.sqrt 2))
  apply (old_signed_flat_plus_partition_oscillation_cap Q 5 b L).trans
  dsimp only [S] at hs
  simp only [old_signed_q1_setup_readable_04,mul_pow,Real.sq_sqrt hs]
  convert hh using 1 <;> dsimp only [r,S,Q] <;> ring

/-- The minus whole-partition oscillation has its own exact endpoint field. -/
theorem old_signed_q1_scaled_minus_oscillation
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let Q := originCube 2 n
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U b L false^2)≤
      theta M*(nativeSetupQ1001FieldsR.getD 5 0)^2 := by
  intro Q b L
  let r := cubeScaleFactor Q/3^5
  let S := nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)
  have hs : 0≤S := mul_nonneg (mul_nonneg old_signed_q1_setup_variance_nonneg (by norm_num)) (by norm_num)
  have hc : planarC0^2≤(11/25:ℝ)^2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) old_signed_q1_planarC0_le 2
  have hgrad : r^2*mainFlatSigmaSq b L≤theta M*S :=
    old_signed_q1_scaled_gradient_energy M h hg n hstate
  have hSigma : 0≤ mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hh := mul_le_mul hc hgrad (mul_nonneg (sq_nonneg r) hSigma) (sq_nonneg (11/25:ℝ))
  apply (old_signed_flat_minus_partition_oscillation_cap Q 5 b L).trans
  dsimp only [S] at hs
  simp only [old_signed_q1_setup_readable_05,mul_pow,Real.sq_sqrt hs]
  convert hh using 1 <;> dsimp only [r,S,Q] <;> ring

end
end ASDExplicitGamma.Native

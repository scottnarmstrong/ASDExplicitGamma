module

public import ASDExplicitGamma.Native.OldSignedQ1RadialCaps
public import ASDExplicitGamma.Native.OldSignedQ1FlatConstants
public import ASDExplicitGamma.Native.OldSignedSourceMultiplier
public import ASDExplicitGamma.Native.OldSignedDerivativeConstants

/-! Actual source and derivative multipliers fit the exact frozen q1 fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The actual complete OLD source multiplier has square-root theta degree
and the SAME endpoint coefficient as the frozen panel. -/
theorem old_signed_q1_scaled_source_multiplier
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    oldSignedSourceMultiplier (originCube 2 n) 5 b L≤
      Real.sqrt (theta M)*(nativeSetupQ1001FieldsR.getD 2 0) := by
  intro b L
  have h0 := old_signed_q1_scaled_amplitude M h hg n hstate
  have h1 := old_signed_q1_scaled_gradient_root M h hg n hstate
  have h2 := old_signed_q1_scaled_hessian_root M h hg n hstate
  have hh := add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1
    (by norm_num : (0:ℝ)≤36/25))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤57/200))
  rw [old_signed_q1_setup_readable_02]
  unfold oldSignedSourceMultiplier diagMeshRadius
  rw [←old_signed_q1_sigma_eq,Real.sqrt_sq_eq_abs]
  convert hh using 1
  · dsimp only [b,L]
    ring
  · ring

/-- The derivative-only source rows fit the frozen outward derivative field,
using their sharper covariance eigenvalues internally. -/
theorem old_signed_q1_scaled_derivative_multiplier
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    oldSignedDerivativeKappa (cubeScaleFactor (originCube 2 n)/3^5) b L.val≤
      Real.sqrt (theta M)*(nativeSetupQ1001FieldsR.getD 3 0) := by
  intro b L
  let r := cubeScaleFactor (originCube 2 n)/3^5
  have hr : 0≤r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have h1 := old_signed_q1_scaled_gradient_root M h hg n hstate
  have h2 := old_signed_q1_scaled_hessian_root M h hg n hstate
  have hv1 : (78/5)*b^2/L.val^2≤mainFlatSigmaSq b L := by
    rw [old_signed_q1_sigma_eq]
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (78/5:ℝ)≤156/5)
      (div_nonneg (sq_nonneg b) (sq_nonneg L.val))
    convert hh using 1 <;> ring
  have hv2 : (23244/25)*b^2/L.val^4≤(46488/25)*b^2/L.val^4 := by
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (23244/25:ℝ)≤46488/25)
      (div_nonneg (sq_nonneg b) (pow_nonneg L.property.le 4))
    convert hh using 1 <;> ring
  have hf := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv1) hr).trans h1
  have hs := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv2) (sq_nonneg r)).trans h2
  have hc : planarC0*planarC1≤(418/3125:ℝ) := by
    have hh := mul_le_mul old_signed_q1_planarC0_le native_boundary_planarC1_le
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤11/25)
    exact hh.trans_eq (by norm_num)
  have hh := add_le_add
    (mul_le_mul old_signed_q1_two_div_pi_le hf (mul_nonneg hr (Real.sqrt_nonneg _))
      (by norm_num : (0:ℝ)≤637/1000))
    (mul_le_mul hc hs (mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg _))
      (by norm_num : (0:ℝ)≤418/3125))
  rw [old_signed_q1_setup_readable_03]
  unfold oldSignedDerivativeKappa
  convert hh using 1
  · dsimp only [r,b,L]
    ring
  · ring

/-- The sharper derivative covariance eigenvalues retain the extra square-root
factor needed by the quadratic OLD weak-history term. -/
theorem old_signed_q1_scaled_derivative_multiplier_sharp
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    Real.sqrt 2*oldSignedDerivativeKappa (cubeScaleFactor (originCube 2 n)/3^5) b L.val ≤
      Real.sqrt (theta M)*(nativeSetupQ1001FieldsR.getD 3 0) := by
  intro b L
  let r := cubeScaleFactor (originCube 2 n)/3^5
  have hr : 0 ≤ r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have h1 := old_signed_q1_scaled_gradient_root M h hg n hstate
  have h2 := old_signed_q1_scaled_hessian_root M h hg n hstate
  have he1 : Real.sqrt 2*Real.sqrt ((78/5)*b^2/L.val^2)=Real.sqrt (mainFlatSigmaSq b L) := by
    rw [←Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num),old_signed_q1_sigma_eq]
    congr 1
    ring
  have he2 : Real.sqrt 2*Real.sqrt ((23244/25)*b^2/L.val^4)=
      Real.sqrt ((46488/25)*b^2/L.val^4) := by
    rw [←Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  have hc : planarC0*planarC1 ≤ (418/3125:ℝ) := by
    have hh := mul_le_mul old_signed_q1_planarC0_le native_boundary_planarC1_le
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 11/25)
    exact hh.trans_eq (by norm_num)
  have hh := add_le_add
    (mul_le_mul old_signed_q1_two_div_pi_le h1 (mul_nonneg hr (Real.sqrt_nonneg _))
      (by norm_num : (0:ℝ) ≤ 637/1000))
    (mul_le_mul hc h2 (mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg _))
      (by norm_num : (0:ℝ) ≤ 418/3125))
  rw [old_signed_q1_setup_readable_03]
  unfold oldSignedDerivativeKappa
  calc
    _ = (2/Real.pi)*(r*Real.sqrt (mainFlatSigmaSq b L))+
        (planarC0*planarC1)*(r^2*Real.sqrt ((46488/25)*b^2/L.val^4)) := by
      rw [←he1,←he2]
      ring
    _ ≤ _ := by convert hh using 1; ring

end
end ASDExplicitGamma.Native

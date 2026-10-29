module

public import ASDExplicitGamma.Native.ParentBoundaryCommonClockTheta

/-! Exact proportional endpoint comparison of every complete-history depth budget. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The source raw affine allowance is monotone in gamma. -/
theorem parent_boundary_common_raw_base_mono
    {gamma eta : ℝ} (hge : gamma ≤ eta) (height r : ℕ) :
    parentBoundaryCommonRawBase gamma height r ≤ parentBoundaryCommonRawBase eta height r := by
  unfold parentBoundaryCommonRawBase
  exact add_le_add_right (mul_le_mul_of_nonneg_right hge (by positivity)) _

/-- The source raw physical frame factor is monotone in gamma. -/
theorem parent_boundary_common_raw_factor_mono
    {gamma eta : ℝ} (hge : gamma ≤ eta) (height r : ℕ) :
    parentBoundaryCommonRawFactor gamma height r ≤ parentBoundaryCommonRawFactor eta height r := by
  unfold parentBoundaryCommonRawFactor
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_left hge (by positivity))) (by norm_num)

private theorem parent_common_source_variance_nonneg
    {gamma : ℝ} (hg : 0 ≤ gamma) (height : ℕ) : 0 ≤ parentBoundaryCommonSourceVariance gamma height := by
  unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
  positivity

/-- The source depth program retains exactly one theta factor under the
endpoint comparison. The remaining positive factors are monotone; no
constant reserve is mistakenly multiplied by theta in isolation. -/
theorem parent_boundary_common_source_depth_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height r j : ℕ) :
    parentBoundaryCommonSourceDepthDrift M.gamma height r j ≤
      theta M*parentBoundaryCommonSourceDepthDrift gammaZero height r j := by
  let K := fun gamma => parentBoundaryCommonKernelProfile
    (parentBoundaryCommonSourceSpatialClock gamma height r 2)
    (parentBoundaryCommonSourceSpatialClock gamma height r 4) ((1/3:ℝ)^j)
  let X := fun gamma =>
    (26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryCommonRawFactor gamma height r*
      (3:ℝ)^(8*gamma*(j:ℝ))*(parentBoundaryCommonRawBase gamma height r+(32474*gamma)*(j:ℝ))+
      (26*48:ℝ)*parentBoundaryCommonSourceVariance gamma height*(3683/2500:ℝ)^3*
        (3:ℝ)^(6*gamma*(j:ℝ))
  have hg0 := M.shellPrefix.gamma_pos.le
  have hzero : (0:ℝ) ≤ gammaZero := by norm_num [gammaZero]
  have hX (gamma : ℝ) (hgamma : 0 ≤ gamma) : 0 ≤ X gamma := by
    have hV := parent_common_source_variance_nonneg hgamma height
    have hF : 0 ≤ parentBoundaryCommonRawFactor gamma height r := by
      unfold parentBoundaryCommonRawFactor
      positivity
    have hA : 0 ≤ parentBoundaryCommonRawBase gamma height r := by
      unfold parentBoundaryCommonRawBase
      positivity
    dsimp only [X]
    positivity
  have hK : K M.gamma ≤ theta M*K gammaZero :=
    parent_boundary_common_source_kernel_theta M hg height r _ (by positivity)
  have hV : parentBoundaryCommonSourceVariance M.gamma height ≤ parentBoundaryCommonSourceVariance gammaZero height :=
    (parent_boundary_common_source_variance_theta M hg height).trans
      ((mul_le_mul_of_nonneg_right (cold_theta_le_one M hg)
        (parent_common_source_variance_nonneg hzero height)).trans_eq (one_mul _))
  have hp (c : ℝ) (hc : 0 ≤ c) : (3:ℝ)^(c*M.gamma*(j:ℝ)) ≤ (3:ℝ)^(c*gammaZero*(j:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hc) (Nat.cast_nonneg j))
  have hF := parent_boundary_common_raw_factor_mono hg height r
  have hraw : parentBoundaryCommonRawBase M.gamma height r+(32474*M.gamma)*(j:ℝ) ≤
      parentBoundaryCommonRawBase gammaZero height r+(32474*gammaZero)*(j:ℝ) :=
    add_le_add (parent_boundary_common_raw_base_mono hg height r)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤32474)) (Nat.cast_nonneg j))
  have hXmono : X M.gamma ≤ X gammaZero := by
    have hF0 : 0 ≤ parentBoundaryCommonRawFactor M.gamma height r := by
      unfold parentBoundaryCommonRawFactor
      positivity
    have hFend : 0 ≤ parentBoundaryCommonRawFactor gammaZero height r := by
      unfold parentBoundaryCommonRawFactor
      positivity
    have hraw0 : 0 ≤ parentBoundaryCommonRawBase M.gamma height r+(32474*M.gamma)*(j:ℝ) := by
      unfold parentBoundaryCommonRawBase
      positivity
    have hV0 := parent_common_source_variance_nonneg hg0 height
    have hVend := parent_common_source_variance_nonneg hzero height
    dsimp only [X]
    apply add_le_add
    · exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) (hp 8 (by norm_num))
          (by positivity) (by positivity)) hraw hraw0 (by positivity)
    · exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) (by norm_num))
        (hp 6 (by norm_num)) (by positivity) (by positivity)
  change K M.gamma*X M.gamma ≤ theta M*(K gammaZero*X gammaZero)
  exact (mul_le_mul hK hXmono (hX M.gamma hg0)
    (mul_nonneg (cold_theta_pos M).le (parent_boundary_common_kernel_profile_nonneg _ _ _))).trans_eq (by ring)

end
end ASDExplicitGamma.Native

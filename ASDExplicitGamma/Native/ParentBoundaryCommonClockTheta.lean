module

public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryDelta
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Exact proportional gamma scaling of the complete source covariance clocks. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Each literal source shell clock retains one exact factor theta. -/
theorem parent_boundary_common_shell_clock_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (s : ℕ) :
    nativeSourceShellClock M.gamma s ≤ theta M*nativeSourceShellClock gammaZero s := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)) (Nat.cast_nonneg s))
  have hc : 0 ≤ (9/2:ℝ)*M.gamma := mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le
  calc
    _ ≤ (9/2:ℝ)*M.gamma*(3:ℝ)^(2*gammaZero*(s:ℝ)) := mul_le_mul_of_nonneg_left hp hc
    _ = _ := by
      dsimp only [theta,nativeSourceShellClock]
      field_simp [show gammaZero ≠ (0:ℝ) by norm_num [gammaZero]]

/-- Both complete finite spatial clocks retain the exact source theta,
with every shell height left inside its own geometric factor. -/
theorem parent_boundary_common_spatial_clock_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height r p : ℕ) :
    parentBoundaryCommonSourceSpatialClock M.gamma height r p ≤
      theta M*parentBoundaryCommonSourceSpatialClock gammaZero height r p := by
  unfold parentBoundaryCommonSourceSpatialClock
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (parent_boundary_common_shell_clock_theta M hg (i.val+1))
    (by positivity)).trans_eq (by ring)

/-- The finite source point-variance clock retains its exact theta factor. -/
theorem parent_boundary_common_source_variance_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) :
    parentBoundaryCommonSourceVariance M.gamma height ≤ theta M*parentBoundaryCommonSourceVariance gammaZero height := by
  unfold parentBoundaryCommonSourceVariance
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => parent_boundary_common_shell_clock_theta M hg (i.val+1))

/-- Exact degree-one homogeneity of the source covariance profile in its
second/fourth clocks, including zero proportional factor. -/
theorem parent_boundary_common_kernel_profile_smul
    (c A2 A4 z : ℝ) (hc : 0 ≤ c) :
    parentBoundaryCommonKernelProfile (c*A2) (c*A4) z=c*parentBoundaryCommonKernelProfile A2 A4 z := by
  calc
    _ = (Real.sqrt c)^2*parentBoundaryCommonKernelProfile A2 A4 z := by
      unfold parentBoundaryCommonKernelProfile
      rw [Real.sqrt_mul hc,Real.sqrt_mul hc]
      ring
    _ = _ := by rw [Real.sq_sqrt hc]

/-- The exact source kernel retains theta before any complete depth sum,
so no nonlinear endpoint substitution loses proportionality. -/
theorem parent_boundary_common_source_kernel_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height r : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
      (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) z ≤
      theta M*parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock gammaZero height r 2)
        (parentBoundaryCommonSourceSpatialClock gammaZero height r 4) z := by
  exact (parent_boundary_common_kernel_profile_mono
    (parent_boundary_common_spatial_clock_theta M hg height r 2)
    (parent_boundary_common_spatial_clock_theta M hg height r 4) hz).trans_eq
      (parent_boundary_common_kernel_profile_smul (theta M) _ _ z (cold_theta_pos M).le)

end
end ASDExplicitGamma.Native

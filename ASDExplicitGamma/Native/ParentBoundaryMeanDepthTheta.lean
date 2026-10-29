module

public import ASDExplicitGamma.Native.ParentBoundaryMeanTheta
public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthSlope

/-! Exact proportional scaling of every physical weak-row mean depth slope. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Every actual source depth slope retains one theta after all frame,
raw-response and covariance factors have been bounded at the endpoint. -/
theorem parent_boundary_mean_depth_slope_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height j : ℕ) :
    parentBoundaryMeanDepthSlope M.gamma height j ≤
      theta M*parentBoundaryMeanDepthSlope gammaZero height j := by
  let b : ℝ := 3683/2500
  let R := fun gamma => (3:ℝ)^(2*gamma*(j:ℝ))
  have hR0 (gamma : ℝ) : 0 ≤ R gamma := by dsimp only [R]; positivity
  have hR : R M.gamma ≤ R gammaZero := Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)) (Nat.cast_nonneg j))
  let F := fun gamma => parentBoundaryCommonRawFactor gamma height (5+j)*parentBoundaryCommonRawBase gamma height (5+j)
  let V := fun gamma => parentBoundaryCommonSourceVariance gamma height
  let K := fun gamma => parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height (5+j) 2
  let A := fun gamma => parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock gamma height (5+j) 2)
    (parentBoundaryCommonSourceSpatialClock gamma height (5+j) 4)
  have htheta := (cold_theta_pos M).le
  have hF0 (gamma : ℝ) (hgamma : 0 ≤ gamma) : 0 ≤ F gamma := by
    dsimp only [F]
    unfold parentBoundaryCommonRawFactor parentBoundaryCommonRawBase
    positivity
  have hF : F M.gamma ≤ F gammaZero := by
    apply mul_le_mul (parent_boundary_common_raw_factor_mono hg height (5+j))
      (parent_boundary_common_raw_base_mono hg height (5+j))
    · have hg0 := M.shellPrefix.gamma_pos.le
      unfold parentBoundaryCommonRawBase
      positivity
    · unfold parentBoundaryCommonRawFactor
      positivity
  have hV : V M.gamma ≤ theta M*V gammaZero := parent_boundary_common_source_variance_theta M hg height
  have hK : K M.gamma ≤ theta M*K gammaZero := by
    exact (mul_le_mul_of_nonneg_left (parent_boundary_common_spatial_clock_theta M hg height (5+j) 2)
      (by unfold parentBoundaryMeanKConstant; positivity)).trans_eq (by dsimp only [K]; ring)
  have hA : (A M.gamma)^2 ≤ theta M*(A gammaZero)^2 := by
    have hm := parent_boundary_mean_a_column_mono
      (parent_boundary_common_spatial_clock_theta M hg height (5+j) 2)
      (parent_boundary_common_spatial_clock_theta M hg height (5+j) 4)
    have ha0 : 0 ≤ A M.gamma := by dsimp only [A]; unfold parentBoundaryMeanAColumn; positivity
    exact (pow_le_pow_left₀ ha0 hm 2).trans_eq
      (parent_boundary_mean_a_column_square_smul _ _ _ htheta)
  have hK0 : 0 ≤ K gammaZero := by
    dsimp only [K]
    unfold parentBoundaryMeanKConstant parentBoundaryCommonSourceSpatialClock nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hb : 0 ≤ b := by norm_num [b]
  have hFend := hF0 gammaZero (by norm_num [gammaZero])
  have hV0 : 0 ≤ V gammaZero := by
    dsimp only [V]
    unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hg0 := M.shellPrefix.gamma_pos.le
  change 2*V M.gamma*R M.gamma*b+2*K M.gamma*R M.gamma*(b*F M.gamma)+
      (232/125:ℝ)*(A M.gamma)^2*(R M.gamma)^2*(b^2*F M.gamma) ≤
    theta M*(2*V gammaZero*R gammaZero*b+2*K gammaZero*R gammaZero*(b*F gammaZero)+
      (232/125:ℝ)*(A gammaZero)^2*(R gammaZero)^2*(b^2*F gammaZero))
  calc
    _ ≤ 2*(theta M*V gammaZero)*R gammaZero*b+
        2*(theta M*K gammaZero)*R gammaZero*(b*F gammaZero)+
        (232/125:ℝ)*(theta M*(A gammaZero)^2)*(R gammaZero)^2*(b^2*F gammaZero) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul
            (mul_le_mul_of_nonneg_left hV (by norm_num)) hR (hR0 M.gamma) (by positivity)) hb
        · exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num)) hR
            (hR0 M.gamma) (by positivity)) (mul_le_mul_of_nonneg_left hF hb)
            (mul_nonneg hb (hF0 M.gamma hg0)) (by positivity)
      · exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num))
          (pow_le_pow_left₀ (hR0 M.gamma) hR 2) (sq_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left hF (sq_nonneg b))
          (mul_nonneg (sq_nonneg _) (hF0 M.gamma hg0)) (by positivity)
    _ = _ := by ring

end
end ASDExplicitGamma.Native

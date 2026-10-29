module

public import ASDExplicitGamma.Native.ParentBoundaryMeanHeatReturn
public import ASDExplicitGamma.Native.ParentBoundaryCommonDepthTheta

/-! Proportional endpoint normalization of the actual physical parent mean slope. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The own-center A-column is monotone in its two nonnegative clock inputs. -/
theorem parent_boundary_mean_a_column_mono {A2 A4 B2 B4 : ℝ}
    (h2 : A2 ≤ B2) (h4 : A4 ≤ B4) :
    parentBoundaryMeanAColumn A2 A4 ≤ parentBoundaryMeanAColumn B2 B4 := by
  unfold parentBoundaryMeanAColumn
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by positivity))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h4) (by positivity))

/-- Its square has exact degree-one covariance homogeneity. -/
theorem parent_boundary_mean_a_column_square_smul (c A2 A4 : ℝ) (hc : 0 ≤ c) :
    (parentBoundaryMeanAColumn (c*A2) (c*A4))^2=c*(parentBoundaryMeanAColumn A2 A4)^2 := by
  unfold parentBoundaryMeanAColumn
  rw [Real.sqrt_mul hc,Real.sqrt_mul hc]
  calc
    _ = (Real.sqrt c)^2*((Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ))*Real.sqrt A2+
        (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*Real.sqrt A4)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

/-- The genuine physical mean slope retains one exact theta, including
both mixed and quadratic covariance columns and all physical frames. -/
theorem parent_boundary_mean_source_slope_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) :
    parentBoundaryMeanSourceSlope M.gamma height ≤
      theta M*parentBoundaryMeanSourceSlope gammaZero height := by
  let b : ℝ := 3683/2500
  let F := fun gamma => parentBoundaryCommonRawFactor gamma height 5*parentBoundaryCommonRawBase gamma height 5
  let V := fun gamma => parentBoundaryCommonSourceVariance gamma height
  let K := fun gamma => parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height 5 2
  let A := fun gamma => parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock gamma height 5 2)
    (parentBoundaryCommonSourceSpatialClock gamma height 5 4)
  have htheta := (cold_theta_pos M).le
  have hF0 (gamma : ℝ) (hgamma : 0 ≤ gamma) : 0 ≤ F gamma := by
    dsimp only [F]
    unfold parentBoundaryCommonRawFactor parentBoundaryCommonRawBase
    positivity
  have hF : F M.gamma ≤ F gammaZero := by
    apply mul_le_mul (parent_boundary_common_raw_factor_mono hg height 5)
      (parent_boundary_common_raw_base_mono hg height 5)
    · have hg0 := M.shellPrefix.gamma_pos.le
      unfold parentBoundaryCommonRawBase
      positivity
    · unfold parentBoundaryCommonRawFactor
      positivity
  have hV : V M.gamma ≤ theta M*V gammaZero := parent_boundary_common_source_variance_theta M hg height
  have hK : K M.gamma ≤ theta M*K gammaZero := by
    exact (mul_le_mul_of_nonneg_left (parent_boundary_common_spatial_clock_theta M hg height 5 2)
      (by unfold parentBoundaryMeanKConstant; positivity)).trans_eq (by dsimp only [K]; ring)
  have hA : (A M.gamma)^2 ≤ theta M*(A gammaZero)^2 := by
    have hm := parent_boundary_mean_a_column_mono
      (parent_boundary_common_spatial_clock_theta M hg height 5 2)
      (parent_boundary_common_spatial_clock_theta M hg height 5 4)
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
  change 2*V M.gamma*b+2*K M.gamma*(b*F M.gamma)+(232/125:ℝ)*(A M.gamma)^2*(b^2*F M.gamma) ≤
    theta M*(2*V gammaZero*b+2*K gammaZero*(b*F gammaZero)+(232/125:ℝ)*(A gammaZero)^2*(b^2*F gammaZero))
  calc
    _ ≤ 2*(theta M*V gammaZero)*b+2*(theta M*K gammaZero)*(b*F gammaZero)+
        (232/125:ℝ)*(theta M*(A gammaZero)^2)*(b^2*F gammaZero) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) hb
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num))
            (mul_le_mul_of_nonneg_left hF hb) (mul_nonneg hb (hF0 M.gamma M.shellPrefix.gamma_pos.le))
            (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_left hF (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) (hF0 M.gamma M.shellPrefix.gamma_pos.le)) (by positivity)
    _ = _ := by ring

end
end ASDExplicitGamma.Native

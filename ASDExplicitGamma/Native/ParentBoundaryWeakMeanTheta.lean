module

public import ASDExplicitGamma.Native.ParentBoundaryWeakMeanSum
public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthTheta

/-! Proportional endpoint comparison of the complete actual weak mean slope. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The complete baseline-weighted source mean slope retains one theta,
including the infinite weak weights and their gamma-dependent frames. -/
theorem parent_boundary_weak_mean_slope_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) :
    parentBoundaryWeakMeanSlope M.gamma height ≤ theta M*parentBoundaryWeakMeanSlope gammaZero height := by
  let f := fun j : ℕ => (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*
    (3:ℝ)^(2*M.gamma*(j:ℝ))*parentBoundaryMeanDepthSlope M.gamma height j
  let g := fun j : ℕ => (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*
    (3:ℝ)^(2*gammaZero*(j:ℝ))*parentBoundaryMeanDepthSlope gammaZero height j
  have hs := parent_boundary_weak_mean_slope_sum M hg height
  have hzero : (0:ℝ) ≤ gammaZero := by norm_num [gammaZero]
  have hgfun : g=parentBoundaryWeakMeanDepthProfile gammaZero height :=
    funext (fun j => parent_boundary_weak_mean_depth_profile_eq gammaZero height j)
  have hgs : Summable g := by
    rw [hgfun]
    exact (parent_boundary_weak_mean_profile_sum hzero le_rfl height).1
  have hpoint (j : ℕ) : f j ≤ theta M*g j := by
    have ha0 := inverse_history_discount_range.1.le
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2)) (Nat.cast_nonneg j))
    have hd := parent_boundary_mean_depth_slope_theta M hg height j
    have hd0 := parent_boundary_mean_depth_slope_nonneg M.shellPrefix.gamma_pos.le height j
    have ht := (cold_theta_pos M).le
    dsimp only [f,g]
    calc
      _ ≤ ((3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*(3:ℝ)^(2*gammaZero*(j:ℝ)))*
          (theta M*parentBoundaryMeanDepthSlope gammaZero height j) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hd hd0 (by positivity)
      _ = _ := by ring
  have hsum := hs.1.tsum_le_tsum hpoint (hgs.mul_left (theta M))
  have hdis0 : 0 ≤ 1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have heend : (1-inverseHistoryDiscount^2)*(∑' j : ℕ,g j)=parentBoundaryWeakMeanSlope gammaZero height := by
    rw [hgfun]
    exact (parent_boundary_weak_mean_profile_sum hzero le_rfl height).2
  rw [←hs.2,←heend]
  exact (mul_le_mul_of_nonneg_left hsum hdis0).trans_eq (by rw [tsum_mul_left]; ring)

end
end ASDExplicitGamma.Native

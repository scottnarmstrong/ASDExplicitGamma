module

public import ASDExplicitGamma.Native.ParentRowFlatProxy

/-! The sharp primitive weak allowance used before exact panel substitution. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Scalar Cold Algsuperdiff.Section3
noncomputable section

/-- The shared primitive weak allowance, including the larger correlated reserve. -/
def parentRowWeakAllowance (height : ℕ) (t : ℝ) : ℝ :=
  (23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+2/10^12

/-- The complete source weak slope is nonnegative before any field comparison. -/
theorem parent_row_weak_slope_nonneg (height : ℕ) :
    0≤parentBoundaryWeakMeanSlope gammaZero height := by
  rw [←(parent_boundary_weak_mean_profile_sum (by norm_num [gammaZero]) le_rfl height).2]
  apply mul_nonneg (sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le
    inverse_history_discount_range.2.le))
  apply tsum_nonneg
  intro j
  rw [←parent_boundary_weak_mean_depth_profile_eq]
  have hs := parent_boundary_mean_depth_slope_nonneg (by norm_num [gammaZero] : (0:ℝ)≤gammaZero) height j
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg inverse_history_discount_range.1.le _)) (Real.rpow_nonneg (by norm_num) _)) hs

/-- The sharp weak allowance is nonnegative throughout physical time. -/
theorem parent_row_weak_allowance_nonneg (height : ℕ) (t : ℝ) (ht : 0≤t) :
    0≤parentRowWeakAllowance height t := by
  unfold parentRowWeakAllowance
  have hs := parent_row_weak_slope_nonneg height
  positivity

end
end ASDExplicitGamma.Native

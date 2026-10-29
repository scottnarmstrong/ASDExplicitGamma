module

public import ASDExplicitGamma.Gaussian.Q3SobolevPointBound
public import ASDExplicitGamma.Gaussian.Q3ContinuousOperator

/-! # C¹ norm control by ordinary H³ on the actual q3 range -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- An explicit ordinary-normalization rectangular Sobolev constant for first jets. -/
noncomputable def rectangleSobolevConstant (a b c d : ℝ) : ℝ :=
  Real.sqrt ((2 / (b - a)) * (2 / (d - c)) + (2 * (b - a)) * (2 / (d - c)) +
    (2 / (b - a)) * (2 * (d - c)) + (2 * (b - a)) * (2 * (d - c)))

theorem c1Index_degree (i : Fin 3) : (c1Index i).1.1.val + (c1Index i).1.2.val ≤ 1 := by
  fin_cases i <;> norm_num [c1Index, h3Zero]

/-- This is a bound on the full uniform first jet, rather than on individual directions. -/
theorem q3C1JetOperator_norm_le (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ‖q3C1JetOperator (closedRectangle a b c d) β L u‖ ≤
      rectangleSobolevConstant a b c d *
        ‖q3SobolevOperator (openRectangle a b c d) β L u‖ := by
  have hA : 0 ≤ 2 / (b - a) := div_nonneg (by norm_num) (sub_pos.mpr hab).le
  have hB : 0 ≤ 2 * (b - a) := mul_nonneg (by norm_num) (sub_pos.mpr hab).le
  have hC : 0 ≤ 2 / (d - c) := div_nonneg (by norm_num) (sub_pos.mpr hcd).le
  have hD : 0 ≤ 2 * (d - c) := mul_nonneg (by norm_num) (sub_pos.mpr hcd).le
  have hS := add_nonneg (add_nonneg (add_nonneg (mul_nonneg hA hC) (mul_nonneg hB hC))
    (mul_nonneg hA hD)) (mul_nonneg hB hD)
  have hbound : 0 ≤ rectangleSobolevConstant a b c d *
      ‖q3SobolevOperator (openRectangle a b c d) β L u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro i
  apply (ContinuousMap.norm_le _ hbound).mpr
  intro x
  change ‖q3Convolution β L (c1Index i) u x.1‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) hbound).mp
  rw [mul_pow, rectangleSobolevConstant, Real.sq_sqrt hS]
  have he : (![x.1 0, x.1 1] : Vec 2) = x.1 := by ext k; fin_cases k <;> rfl
  have hh := q3Convolution_point_sq_le a b c d β hab hcd L u (c1Index i)
    (c1Index_degree i) (x.1 0) (x.1 1) x.2.1 x.2.2
  rw [he] at hh
  simpa only [Real.norm_eq_abs, sq_abs] using hh

end ASDExplicitGamma.Gaussian

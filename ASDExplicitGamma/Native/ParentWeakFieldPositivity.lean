module

public import ASDExplicitGamma.Native.ParentWeakFieldValue

/-! Positivity of the literal source weak slope's complete geometric terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Cold Algsuperdiff.Section3
noncomputable section

/-- The exact source affine-geometric term is nonnegative at every spatial degree. -/
theorem parent_weak_field_geo_nonneg (height : ℕ) (growth : ℝ) (hgrowth : growth ≤ 10) (degree : ℕ) :
    0 ≤ parentBoundaryWeakGeo gammaZero growth degree
      (parentBoundaryCommonRawBase gammaZero height 5) (32474*gammaZero) := by
  have hq := parent_boundary_weak_ratio_range (by norm_num [gammaZero]) le_rfl growth hgrowth degree
  have hU : 0 ≤ parentBoundaryCommonRawBase gammaZero height 5 := by
    unfold parentBoundaryCommonRawBase
    norm_num [gammaZero]
    positivity
  unfold parentBoundaryWeakGeo
  exact add_nonneg (div_nonneg hU (sub_pos.mpr hq.2).le)
    (div_nonneg (mul_nonneg (by norm_num [gammaZero]) hq.1) (sq_nonneg _))

/-- The unchanged original rare correction also has a strict geometric ratio. -/
theorem parent_weak_field_rare_ratio_lt_one :
    inverseHistoryDiscount^2*(3:ℝ)^(4*gammaZero+1/64) < 1 := by
  rw [inverse_history_discount_power,←Real.rpow_add (by norm_num : (0:ℝ)<3)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num [gammaZero])

/-- The source Young and center-variance allowances dominate the direct
physical raw-response payment. All clocks here are their literal source values. -/
theorem parent_weak_field_young_payment_le (height p degree : ℕ)
    (growth centerGrowth : ℝ) (hgrowth : growth ≤ 10) (hcenter : centerGrowth ≤ 10) :
    (3683/2500:ℝ)^p*parentBoundaryCommonRawFactor gammaZero height 5*
      parentBoundaryWeakGeo gammaZero growth degree
        (parentBoundaryCommonRawBase gammaZero height 5) (32474*gammaZero) ≤
    (26/25:ℝ)*(3683/2500:ℝ)^p*parentBoundaryCommonRawFactor gammaZero height 5*
      parentBoundaryWeakGeo gammaZero growth degree
        (parentBoundaryCommonRawBase gammaZero height 5) (32474*gammaZero)+
      52*parentBoundaryCommonSourceVariance gammaZero height*Real.sqrt 3*(3683/2500:ℝ)^(p+1)/
        (1-parentBoundaryWeakRatio gammaZero centerGrowth degree) := by
  have hF : 0 ≤ parentBoundaryCommonRawFactor gammaZero height 5 := by
    unfold parentBoundaryCommonRawFactor
    positivity
  have hv : 0 ≤ parentBoundaryCommonSourceVariance gammaZero height := by
    unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hq := parent_boundary_weak_ratio_range (by norm_num [gammaZero]) le_rfl centerGrowth hcenter degree
  have hbase := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤3683/2500) p) hF)
    (parent_weak_field_geo_nonneg height growth hgrowth degree)
  have hscale := mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)≤26/25) hbase
  simp only [one_mul,←mul_assoc] at hscale
  exact hscale.trans (le_add_of_nonneg_right (div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv) (Real.sqrt_nonneg _))
      (pow_nonneg (by norm_num) _)) (sub_pos.mpr hq.2).le))

end
end ASDExplicitGamma.Native

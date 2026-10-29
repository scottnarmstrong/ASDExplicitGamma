module

public import ASDExplicitGamma.Native.ParentWeakFieldPositivity

/-! The literal stored Young/variance allowances dominate the direct
physical weak slope, with every complete spatial degree retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Cold Algsuperdiff.Section3
noncomputable section

/-- The primitive weak slope is below the exact unrounded source program.
Only positive Young, center-variance and rare terms are added. -/
theorem parent_weak_field_primitive_le_value (height : ℕ) :
    parentBoundaryWeakMeanSlope gammaZero height ≤ parentWeakFieldSlopeValue height := by
  let b : ℝ := 3683/2500
  let F := parentBoundaryCommonRawFactor gammaZero height 5
  let U := parentBoundaryCommonRawBase gammaZero height 5
  let V := 32474*gammaZero
  let v := parentBoundaryCommonSourceVariance gammaZero height
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gammaZero height 5 2
  let C := parentBoundaryWeakMeanCoefficients gammaZero height
  let qr := inverseHistoryDiscount^2*(3:ℝ)^(4*gammaZero+1/64)
  have hdis : 0 ≤ 1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hv : 0 ≤ v := by
    unfold v parentBoundaryCommonSourceVariance nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hK : 0 ≤ K := by
    unfold K parentBoundaryMeanKConstant parentBoundaryCommonSourceSpatialClock nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hsum : (∑ i : Fin 3,C i*b^3*F*parentBoundaryWeakGeo gammaZero 10 (i.val+2) U V) ≤
      ∑ i : Fin 3,C i*((26/25:ℝ)*b^3*F*parentBoundaryWeakGeo gammaZero 10 (i.val+2) U V+
        52*v*Real.sqrt 3*b^4/(1-parentBoundaryWeakRatio gammaZero 8 (i.val+2))) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (parent_weak_field_young_payment_le height 3 (i.val+2) 10 8 le_rfl (by norm_num))
      (parent_boundary_weak_mean_coefficients_nonneg gammaZero height i)
    simpa only [C,b,F,U,V,v,mul_assoc] using hh
  have hmix : (2*K*b^2*F)*parentBoundaryWeakGeo gammaZero 8 2 U V ≤
      2*K*((26/25:ℝ)*b^2*F*parentBoundaryWeakGeo gammaZero 8 2 U V+
        52*v*Real.sqrt 3*b^3/(1-parentBoundaryWeakRatio gammaZero 6 2)) := by
    have hh := mul_le_mul_of_nonneg_left
      (parent_weak_field_young_payment_le height 2 2 8 6 (by norm_num) (by norm_num))
      (mul_nonneg (by norm_num : (0:ℝ)≤2) hK)
    simpa only [b,F,U,V,v,mul_assoc] using hh
  have hrare : 0 ≤ 2*v*b*Real.sqrt 3*(3/10^46)/(1-qr) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv)
      (by norm_num [b])) (Real.sqrt_nonneg _)) (by norm_num))
      (sub_pos.mpr parent_weak_field_rare_ratio_lt_one).le
  change (1-inverseHistoryDiscount^2)*
    ((∑ i : Fin 3,C i*b^3*F*parentBoundaryWeakGeo gammaZero 10 (i.val+2) U V)+
      (2*K*b^2*F)*parentBoundaryWeakGeo gammaZero 8 2 U V+
      (2*v*b^2)/(1-parentBoundaryWeakRatio gammaZero 4 0)) ≤ _
  apply mul_le_mul_of_nonneg_left _ hdis
  exact (add_le_add (add_le_add hsum hmix) le_rfl).trans (le_add_of_nonneg_right hrare)

end
end ASDExplicitGamma.Native

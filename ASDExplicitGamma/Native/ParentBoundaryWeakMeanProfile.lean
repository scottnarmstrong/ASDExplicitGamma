module

public import ASDExplicitGamma.Native.ParentBoundaryWeakGeometric

/-! Exact source polynomial for the complete baseline-weighted parent weak mean slope. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The three own-center covariance degrees of the source weak mean bill. -/
def parentBoundaryWeakMeanCoefficients (gamma : ℝ) (height : ℕ) : Fin 3 → ℝ :=
  let a := (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ))*
    Real.sqrt (parentBoundaryCommonSourceSpatialClock gamma height 5 2)
  let d := (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*
    Real.sqrt (parentBoundaryCommonSourceSpatialClock gamma height 5 4)
  ![(232/125:ℝ)*a^2,(464/125:ℝ)*a*d,(232/125:ℝ)*d^2]

/-- The literal source weak mean slope at each infinite depth, expressed
as the three covariance degrees plus the mixed and inverse terms. -/
def parentBoundaryWeakMeanDepthProfile (gamma : ℝ) (height j : ℕ) : ℝ :=
  let b : ℝ := 3683/2500
  let U := parentBoundaryCommonRawBase gamma height 5
  let V := 32474*gamma
  let F := parentBoundaryCommonRawFactor gamma height 5
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height 5 2
  let S := parentBoundaryCommonSourceVariance gamma height
  (∑ i : Fin 3,parentBoundaryWeakMeanCoefficients gamma height i*b^3*F*
    (parentBoundaryWeakRatio gamma 10 (i.val+2))^j*(U+V*(j:ℝ)))+
    (2*K*b^2*F)*(parentBoundaryWeakRatio gamma 8 2)^j*(U+V*(j:ℝ))+
    (2*S*b^2)*(parentBoundaryWeakRatio gamma 4 0)^j

/-- Every own-center covariance coefficient is nonnegative, independently
of a sign assumption on gamma. -/
theorem parent_boundary_weak_mean_coefficients_nonneg (gamma : ℝ) (height : ℕ) (i : Fin 3) :
    0 ≤ parentBoundaryWeakMeanCoefficients gamma height i := by
  fin_cases i <;> norm_num [parentBoundaryWeakMeanCoefficients] <;> positivity

/-- The exact baseline-weighted physical depth slope is the source
polynomial, keeping all infinite depths and every physical frame factor. -/
theorem parent_boundary_weak_mean_depth_profile_eq
    (gamma : ℝ) (height j : ℕ) :
    (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*(3:ℝ)^(2*gamma*(j:ℝ))*
      parentBoundaryMeanDepthSlope gamma height j=
      parentBoundaryWeakMeanDepthProfile gamma height j := by
  let R := (3:ℝ)^(2*gamma*(j:ℝ))
  have hp (k : ℕ) : (3:ℝ)^(((2:ℝ)*(k:ℝ))*gamma*(j:ℝ))=R^k := by
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  have h4 : (3:ℝ)^(4*gamma*(j:ℝ))=R^2 := by convert hp 2 using 1; norm_num
  have h8 : (3:ℝ)^(8*gamma*(j:ℝ))=R^4 := by convert hp 4 using 1; norm_num
  have h10 : (3:ℝ)^(10*gamma*(j:ℝ))=R^5 := by convert hp 5 using 1; norm_num
  have hFeq : parentBoundaryCommonRawFactor gamma height (5+j)*parentBoundaryCommonRawBase gamma height (5+j)=
      parentBoundaryCommonRawFactor gamma height 5*(3:ℝ)^(4*gamma*(j:ℝ))*
        (parentBoundaryCommonRawBase gamma height 5+(32474*gamma)*(j:ℝ)) := by
    unfold parentBoundaryCommonRawFactor parentBoundaryCommonRawBase
    push_cast
    have he : (2*(height:ℝ)+4*((5:ℝ)+(j:ℝ))+4)*gamma=
        (2*(height:ℝ)+4*5+4)*gamma+4*gamma*(j:ℝ) := by ring
    rw [he,Real.rpow_add (by norm_num : (0:ℝ)<3)]
    ring
  have hr (growth : ℝ) (degree : ℕ) := (parent_boundary_weak_ratio_power gamma growth degree j).symm
  unfold parentBoundaryWeakMeanDepthProfile
  simp only [Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two]
  rw [hr 10 2,hr 10 3,hr 10 4,hr 8 2,hr 4 0]
  unfold parentBoundaryMeanDepthSlope
  rw [hFeq,parent_boundary_mean_a_column_depth,parent_boundary_mean_source_clock_depth]
  rw [h4,h8,h10]
  norm_num [parentBoundaryWeakMeanCoefficients]
  dsimp only [R]
  ring

end
end ASDExplicitGamma.Native

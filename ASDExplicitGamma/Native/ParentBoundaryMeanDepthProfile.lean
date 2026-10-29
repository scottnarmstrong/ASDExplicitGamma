module

public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthSlope
public import ASDExplicitGamma.Native.ParentBoundaryMeanTheta

/-! Exact spatial depth factors in the complete physical source mean profile. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Every finite covariance clock has its exact spatial depth factor. -/
theorem parent_boundary_mean_source_clock_depth
    (gamma : ℝ) (height r j p : ℕ) :
    parentBoundaryCommonSourceSpatialClock gamma height (r+j) p=
      parentBoundaryCommonSourceSpatialClock gamma height r p*((1/3:ℝ)^j)^p := by
  unfold parentBoundaryCommonSourceSpatialClock
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have he : r+j+(i.val+1)=r+(i.val+1)+j := by omega
  rw [he,Nat.add_mul,pow_add,pow_mul]
  ring

/-- The own-center mean A-column at relative depth j has exactly the
linear/quadratic spatial polynomial of the source program. -/
theorem parent_boundary_mean_a_column_depth
    (gamma : ℝ) (height r j : ℕ) :
    parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock gamma height (r+j) 2)
      (parentBoundaryCommonSourceSpatialClock gamma height (r+j) 4)=
      (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ))*
        Real.sqrt (parentBoundaryCommonSourceSpatialClock gamma height r 2)*(1/3:ℝ)^j+
      (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*
        Real.sqrt (parentBoundaryCommonSourceSpatialClock gamma height r 4)*((1/3:ℝ)^j)^2 := by
  rw [parent_boundary_mean_source_clock_depth,parent_boundary_mean_source_clock_depth]
  unfold parentBoundaryMeanAColumn
  rw [Real.sqrt_mul' _ (sq_nonneg ((1/3:ℝ)^j))]
  rw [Real.sqrt_mul' _ (by positivity : (0:ℝ) ≤ ((1/3:ℝ)^j)^4)]
  rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ (1/3:ℝ)^j)]
  have hfour : ((1/3:ℝ)^j)^4=(((1/3:ℝ)^j)^2)^2 := by ring
  rw [hfour,Real.sqrt_sq (sq_nonneg _)]
  ring

end
end ASDExplicitGamma.Native

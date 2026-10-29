module

public import ASDExplicitGamma.Native.ParentBoundaryMeanGenerator
public import ASDExplicitGamma.Native.ParentBoundaryMeanCoefficientBudget
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRawProfile

/-! Actual finite-band mean slope with the exact source spatial covariance budgets. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The direct physical source mean slope. Its full-response factors are
no larger than the source Young J0/Kj0 payment used by the parent panels. -/
def parentBoundaryMeanSourceSlope (gamma : ℝ) (height : ℕ) : ℝ :=
  let b : ℝ := 3683/2500
  let F := parentBoundaryCommonRawFactor gamma height 5*parentBoundaryCommonRawBase gamma height 5
  let V := parentBoundaryCommonSourceVariance gamma height
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height 5 2
  let A := parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock gamma height 5 2)
    (parentBoundaryCommonSourceSpatialClock gamma height 5 4)
  2*V*b+2*K*(b*F)+(232/125:ℝ)*A^2*(b^2*F)

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.ParentBoundaryMeanGeometry
public import ASDExplicitGamma.Native.ParentBoundaryCommonSourceKernel

/-! Exact finite source covariance and mixed-direction budgets for parent cell means. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The source A-column sum at its own center, retaining the second/fourth
spatial covariance clocks separately. -/
def parentBoundaryMeanAColumn (A2 A4 : ℝ) : ℝ :=
  (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ))*Real.sqrt A2+
    (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*Real.sqrt A4

/-- The whole-square deterministic mixed source coefficient. -/
def parentBoundaryMeanKConstant : ℝ :=
  (78/5:ℝ)*((1/4:ℝ)+(36/25:ℝ)/Real.sqrt 2+(57/200:ℝ)*Real.sqrt 2)

end
end ASDExplicitGamma.Native

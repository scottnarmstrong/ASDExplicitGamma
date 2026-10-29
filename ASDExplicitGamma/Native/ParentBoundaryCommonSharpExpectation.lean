module

public import ASDExplicitGamma.Native.ParentBoundaryCommonFullBank
public import ASDExplicitGamma.Native.ParentBoundaryCommonPowerExpectation
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterMoment64
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHolder
public import ASDExplicitGamma.Native.ParentBoundaryPopulationBankL256

/-! Sharp actual common-center shell expectation with the source center-error payment. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Actual finite fresh-band variance in the fixed starting true frame. -/
def parentBoundaryCommonBandVariance (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) : ℝ :=
  (∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2)/
    (Annealed.sigmaBar M n:ℝ)^2

/-- The literal variance clock is nonnegative. -/
theorem parent_boundary_common_band_variance_nonneg (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) :
    0 ≤ parentBoundaryCommonBandVariance M h n height := by
  unfold parentBoundaryCommonBandVariance
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)

end
end ASDExplicitGamma.Native

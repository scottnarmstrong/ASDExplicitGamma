module

public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedHistory
public import ASDExplicitGamma.Native.ParentBoundaryCommonKernelGeometricSum
public import ASDExplicitGamma.Scalar.StructuralContinuity

/-! Literal source full-response and variance profiles for complete history drift. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Source finite fresh-band variance clock, preserving shell heights. -/
def parentBoundaryCommonSourceVariance (gamma : ℝ) (height : ℕ) : ℝ :=
  ∑ i : Fin height,nativeSourceShellClock gamma (i.val+1)

/-- Literal fixed-depth affine raw response allowance. -/
def parentBoundaryCommonRawBase (gamma : ℝ) (height r : ℕ) : ℝ :=
  (1009309/500000:ℝ)+gamma*(32474*((height:ℝ)+(r:ℝ)+1)+11483216)

/-- Literal fixed-depth full-response frame factor. -/
def parentBoundaryCommonRawFactor (gamma : ℝ) (height r : ℕ) : ℝ :=
  4*(3:ℝ)^((2*(height:ℝ)+4*(r:ℝ)+4)*gamma)

/-- The exact source depth-drift majorant before summing any depth. -/
def parentBoundaryCommonSourceDepthDrift (gamma : ℝ) (height r j : ℕ) : ℝ :=
  parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock gamma height r 2)
    (parentBoundaryCommonSourceSpatialClock gamma height r 4) ((1/3:ℝ)^j)*
      ((26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryCommonRawFactor gamma height r*
        (3:ℝ)^(8*gamma*(j:ℝ))*(parentBoundaryCommonRawBase gamma height r+(32474*gamma)*(j:ℝ))+
        (26*48:ℝ)*parentBoundaryCommonSourceVariance gamma height*(3683/2500:ℝ)^3*
          (3:ℝ)^(6*gamma*(j:ℝ)))

/-- Exact actual true-frame comparison for the protected observer n-j. -/
theorem parent_boundary_common_protected_frame_depth (M : ABKModel 2) (n : ℤ) (j : ℕ) :
    0 ≤ (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ) ∧
      (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ) ≤ (3:ℝ)^(2*M.gamma*(j:ℝ)) := by
  constructor
  · exact div_nonneg (Annealed.sigmaBar_characterization M n).1.le
      (Annealed.sigmaBar_characterization M (n-(j:ℤ))).1.le
  · have hh := (sigmaBar_structural_continuity_nat M (n-(j:ℤ)) j).2
    rw [sub_add_cancel] at hh
    exact hh

/-- The actual physical full-response bank is exactly the affine-depth
source raw profile times its explicit depth growth. -/
theorem parent_boundary_common_raw_profile_eq (M : ABKModel 2) (height r j : ℕ) :
    parentBoundaryBandTraceCap M height (r+j)=parentBoundaryCommonRawFactor M.gamma height r*
      (3:ℝ)^(4*M.gamma*(j:ℝ))*(parentBoundaryCommonRawBase M.gamma height r+(32474*M.gamma)*(j:ℝ)) := by
  rw [parent_boundary_band_trace_cap_factor]
  dsimp only [parentBoundaryCommonRawFactor,parentBoundaryCommonRawBase]
  ring

/-- All source depth drift terms are nonnegative, before summing. -/
theorem parent_boundary_common_source_depth_drift_nonneg
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (height r j : ℕ) :
    0 ≤ parentBoundaryCommonSourceDepthDrift gamma height r j := by
  have hv : 0 ≤ parentBoundaryCommonSourceVariance gamma height := by
    unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
    positivity
  have hA : 0 ≤ parentBoundaryCommonRawBase gamma height r := by
    unfold parentBoundaryCommonRawBase
    positivity
  have hF : 0 ≤ parentBoundaryCommonRawFactor gamma height r := by
    unfold parentBoundaryCommonRawFactor
    positivity
  have hK := parent_boundary_common_kernel_profile_nonneg
    (parentBoundaryCommonSourceSpatialClock gamma height r 2)
    (parentBoundaryCommonSourceSpatialClock gamma height r 4) ((1/3:ℝ)^j)
  unfold parentBoundaryCommonSourceDepthDrift
  positivity

end
end ASDExplicitGamma.Native

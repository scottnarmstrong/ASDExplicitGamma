module

public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedFullBank
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandTrace
public import ASDExplicitGamma.Native.GenericSourceActualInverse

/-! The exact physical observer bank for source mean heat, anchored in the starting frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The generic source-square restriction is literally the existing
physical observer coefficient on an origin square. -/
theorem parent_boundary_mean_observer_coefficient_eq
    (q n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryCommonOpenCubeCoefficient (originCube 2 q)
      (parentBoundaryCommonCubeBand (originCube 2 q) n height t ω)=
        pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω) := by
  ext x
  rfl

end
end ASDExplicitGamma.Native

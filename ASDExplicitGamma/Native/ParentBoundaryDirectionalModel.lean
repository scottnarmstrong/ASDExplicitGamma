module

public import ASDExplicitGamma.Native.ParentBoundaryDirectionalGenerator
public import ASDExplicitGamma.Native.OldSignedModelTraceBridge

/-! The parent-gauge refinement for the literal closed-cube model heat
observable, with the physical fresh amplitude restored. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse
noncomputable section

/-- Actual model heat trace bound, with no generator estimate premise.
Its full flat baseline and signed inverse coefficient Y are retained. -/
theorem parent_boundary_directional_model_generator (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (x : C(closure (cubeSet (originCube 2 m)),ℝ))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let k := pureFluxOpenResponseRestriction m x
    let a := responseFramePlanarCoefficientField nu sigma k
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q depth a b L-
      parentBoundaryDirichletEnergy Q b L*
        (Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      descendantsAverage Q depth (fun U => parentBoundaryDirectionalCellError Q U nu sigma hnu hsigma k b L) := by
  intro Q k a
  rw [old_signed_model_trace_generator_eq m nu sigma hnu hsigma b L x]
  exact (parent_boundary_directional_signed_generator m depth nu sigma hnu hsigma k b L).2

end
end ASDExplicitGamma.Native

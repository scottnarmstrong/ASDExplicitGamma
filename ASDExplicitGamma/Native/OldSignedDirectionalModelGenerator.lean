module

public import ASDExplicitGamma.Native.OldSignedDirectionalGenerator
public import ASDExplicitGamma.Native.OldSignedModelTraceBridge

/-! Directional AN (5.3) for the actual closed-cube model heat generator, at its true
physical amplitude. The open-cube coefficient is the exact restriction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse
noncomputable section

/-- The physical q3 model generator at amplitude sigma b obeys the OLD
signed bound. This is the exact source observable used by the heat return. -/
theorem native_boundary_old_signed_model_generator_directional (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (x : C(closure (cubeSet (originCube 2 m)),ℝ))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let k := pureFluxOpenResponseRestriction m x
    let a := responseFramePlanarCoefficientField nu sigma k
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q mesh a b L-
      b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      descendantsAverage Q mesh (fun U => oldSignedDirectionalCellError Q U mesh nu sigma hnu hsigma k b L) := by
  intro Q k a
  rw [old_signed_model_trace_generator_eq m nu sigma hnu hsigma b L x]
  exact (native_boundary_old_signed_generator_directional m mesh nu sigma hnu hsigma k b L).2

end
end ASDExplicitGamma.Native

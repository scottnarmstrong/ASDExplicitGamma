module

public import ASDExplicitGamma.Native.OldSignedDirectionalModelGenerator
public import ASDExplicitGamma.Native.OldSignedAffineExpectation
public import ASDExplicitGamma.Native.GenericSourceBandMeanHeat
public import ASDExplicitGamma.Native.ParentBoundaryInverseBandDrift

/-! Exact one-shell carriers for the signed OLD heat generator and inverse trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Restriction to the open cube and normalization produce exactly the
physical closed-cube coarse matrix in its scalar frame. -/
theorem old_signed_open_coarse_frame (n : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    coarseBlockMatrix (openCubeSet (originCube 2 n))
      (responseFramePlanarCoefficientField nu sigma (pureFluxOpenResponseRestriction n x))=
      frameMatrix sigma (coarseBlockMatrix (cubeSet (originCube 2 n))
        (responsePlanarCoefficientField nu (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x))) := by
  rw [coarseBlockMatrix_congr_of_ae_eq (pureFluxOpenResponseRestriction_frame_ae n nu sigma x hsigma)]
  rw [←cold_coarse_cube_open (originCube 2 n)]
  exact cold_coarse_frame hnu (responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet (originCube 2 n)) nu hnu
    (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x)) hsigma

end
end ASDExplicitGamma.Native

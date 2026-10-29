module

public import ASDExplicitGamma.Native.OldSignedShearFieldTransport

/-! Exact signed shear feedback against the actual canonical reciprocal
potential in the true scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual reciprocal H1 potential in the fixed true response frame. -/
def oldSignedFrameReciprocalPotential (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    H1Function (openCubeSet Q) :=
  oldSignedReciprocalPotential Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P

/-- Its gradient is exactly the physical second coefficient block. -/
theorem old_signed_frame_reciprocal_potential_grad (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k P).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2 :=
  old_signed_reciprocal_potential_grad Q _ _ P

end
end ASDExplicitGamma.Native

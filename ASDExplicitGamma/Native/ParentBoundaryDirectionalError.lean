module

public import ASDExplicitGamma.Native.OldSignedDirectionalErrorBill
public import ASDExplicitGamma.Native.ParentBoundarySourceBudget
public import ASDExplicitGamma.Native.ParentBoundaryCentering
public import ASDExplicitGamma.Native.OldSignedErrorBill

/-! Literal directional parent-gauge error, with the actual parent source
and centered complete covariances. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Response Scalar Triadic
noncomputable section

/-- The actual local Err_U in the same physical frame as the parent
minimizers. Histories use the actual parent coefficient on U and all its
contained descendants; they are never reset to a different medium. -/
def parentBoundaryDirectionalCellError (Q U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  oldSignedDirectionalErrorBill
    (oldSignedInverseHistory U a)
    (oldSignedResponseHistory U a)
    (oldSignedCorrectorHistory U a)
    (oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k)
    (oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)
    (parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L)
    (oldSignedFlatDirectionalMeanProxy Q U a b L true)
    (oldSignedFlatDirectionalMeanProxy Q U a b L false)
    (oldSignedFlatL2Size Q U b L false)
    (oldSignedFlatOscillationSize Q U b L true)
    (oldSignedFlatOscillationSize Q U b L false)
    (parentBoundaryCenteredBeta Q U b L true)
    (parentBoundaryCenteredBeta Q U b L false)
    (oldSignedDerivativeKappa (cubeScaleFactor U) b L.1)

end
end ASDExplicitGamma.Native

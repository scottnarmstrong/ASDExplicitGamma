module

public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles
public import ASDExplicitGamma.Native.OldSignedFlatCovarianceFeedback
public import ASDExplicitGamma.Native.OldSignedDerivativeConstants

/-! Exact AN (5.1) error bill, with actual local profiles and histories.
No product of old-medium factors is replaced by independent factors. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- Literal scalar expression of AN (5.1). D is 1+alpha and Cminus is
sqrt(B M)+1; the later derivative feedback and both covariance terms stay. -/
def oldSignedErrorBill (B M theta V G d x y Oplus Ominus betaPlus betaMinus kappa : ℝ) : ℝ :=
  let D := 1+Scalar.inverseHistoryDiscount
  let Cminus := Real.sqrt (B*M)+1
  2*Real.sqrt (6*theta)*(x*Oplus+y*Ominus)+M*(Oplus^2+Ominus^2)+B*d^2+
    2*d*(Real.sqrt (6*theta)*(x+y)+(M+1)*(Oplus+Ominus))+
    2*(betaPlus*V+betaMinus*G)+
    2*kappa*(G*(Real.sqrt theta*x+D*B*Oplus)+
      (Real.sqrt 2+G)*D*B*d+
      (Real.sqrt 2+G)*(Real.sqrt theta*y+Cminus*Ominus))

/-- The actual local Err_U in the same physical frame as the parent
minimizers. Histories use the actual parent coefficient on U and all its
contained descendants; they are never reset to a different medium. -/
def oldSignedCellError (Q U : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  oldSignedErrorBill
    (oldSignedInverseHistory U a)
    (oldSignedResponseHistory U a)
    (oldSignedCorrectorHistory U a)
    (oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k)
    (oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)
    (oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L)
    (oldSignedFlatL2Size Q U b L true)
    (oldSignedFlatL2Size Q U b L false)
    (oldSignedFlatOscillationSize Q U b L true)
    (oldSignedFlatOscillationSize Q U b L false)
    (oldSignedCovarianceBeta Q U b L true)
    (oldSignedCovarianceBeta Q U b L false)
    (oldSignedDerivativeKappa (cubeScaleFactor U) b L.1)

end
end ASDExplicitGamma.Native

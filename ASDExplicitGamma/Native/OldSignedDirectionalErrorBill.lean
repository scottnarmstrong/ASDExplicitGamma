module

public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles
public import ASDExplicitGamma.Native.OldSignedFlatCovarianceFeedback
public import ASDExplicitGamma.Native.OldSignedDerivativeConstants
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy

/-! Directional refinement of the AN (5.1) error bill, with actual local profiles and histories.
No product of old-medium factors is replaced by independent factors. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- Directional scalar bill of the actual AN trial. D is 1+alpha and Cminus is
sqrt(B M)+1; the later derivative feedback and both covariance terms stay. -/
def oldSignedDirectionalErrorBill (B M theta V G d Pplus Pminus y Oplus Ominus betaPlus betaMinus kappa : ℝ) : ℝ :=
  (2*Real.sqrt Pplus*Oplus+B*Oplus^2+2*Real.sqrt (2*theta)*(y*Ominus)+M*Ominus^2)+B*d^2+
    2*(d*(Real.sqrt (Pplus+Pminus)+Real.sqrt ((B+1)^2*Oplus^2+B*M*Ominus^2)))+
    2*(kappa*G*(Real.sqrt Pplus+(1+inverseHistoryDiscount)*B*Oplus))+
    2*(kappa*(Real.sqrt 2+G)*((1+inverseHistoryDiscount)*B*d))+
    2*(kappa*(Real.sqrt 2+G)*(Real.sqrt Pminus+(Real.sqrt (B*M)+1)*Ominus))+
    2*(betaPlus*V)+2*(betaMinus*G)

/-- The actual local Err_U in the same physical frame as the parent
minimizers. Histories use the actual parent coefficient on U and all its
contained descendants; they are never reset to a different medium. -/
def oldSignedDirectionalCellError (Q U : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  oldSignedDirectionalErrorBill
    (oldSignedInverseHistory U a)
    (oldSignedResponseHistory U a)
    (oldSignedCorrectorHistory U a)
    (oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k)
    (oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)
    (oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L)
    (oldSignedFlatDirectionalMeanProxy Q U a b L true)
    (oldSignedFlatDirectionalMeanProxy Q U a b L false)
    (oldSignedFlatL2Size Q U b L false)
    (oldSignedFlatOscillationSize Q U b L true)
    (oldSignedFlatOscillationSize Q U b L false)
    (oldSignedCovarianceBeta Q U b L true)
    (oldSignedCovarianceBeta Q U b L false)
    (oldSignedDerivativeKappa (cubeScaleFactor U) b L.1)

end
end ASDExplicitGamma.Native

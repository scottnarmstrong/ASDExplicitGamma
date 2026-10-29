module

public import ASDExplicitGamma.Main.ELinearPathwise
public import ASDExplicitGamma.Native.OldSignedHalfGainBill
public import ASDExplicitGamma.Native.OldSignedDirectionalTrialTotalBound

/-! Samplewise majorant of the exact `L` group of the actual OLD-frame local
trial, assembled from the directional flat, plus-feedback and minus-feedback
bills, before any expectation is taken. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Plus-feedback part of the pathwise majorant. -/
def mainELinearPlusFeedbackHalfGainMajorant (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  descendantsAverage Q depth (fun U =>
    oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k *
      (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true) +
        (1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a *
          oldSignedFlatOscillationSize Q U b L true))

end

end ASDExplicitGamma.Main

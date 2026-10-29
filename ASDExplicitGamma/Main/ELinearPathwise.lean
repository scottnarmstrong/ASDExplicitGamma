module

public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Native.OldSignedTrialTotalBound
public import Algsuperdiff.Section3.Model
public import Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
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

/-- Flat part of the pathwise majorant: the four local flat terms averaged
over the depth-five cells. -/
def mainELinearFlatMajorant (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  descendantsAverage Q depth (fun U =>
    2 * Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true) *
        oldSignedFlatOscillationSize Q U b L true +
      oldSignedInverseHistory U a * oldSignedFlatOscillationSize Q U b L true ^ 2 +
      2 * Real.sqrt (2 * oldSignedCorrectorHistory U a) *
        (oldSignedFlatL2Size Q U b L false *
          oldSignedFlatOscillationSize Q U b L false) +
      oldSignedResponseHistory U a * oldSignedFlatOscillationSize Q U b L false ^ 2)

/-- Minus-feedback part of the pathwise majorant. -/
def mainELinearMinusFeedbackMajorant (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  descendantsAverage Q depth (fun U =>
    oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
      (Real.sqrt 2 + oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k) *
      (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L false) +
        (Real.sqrt (oldSignedInverseHistory U a * oldSignedResponseHistory U a) + 1) *
          oldSignedFlatOscillationSize Q U b L false))

end

end ASDExplicitGamma.Main

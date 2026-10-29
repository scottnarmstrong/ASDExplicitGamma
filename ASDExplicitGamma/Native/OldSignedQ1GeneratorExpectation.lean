module

public import ASDExplicitGamma.Native.OldSignedQ1GeneratorCarrier
public import ASDExplicitGamma.Native.OldSignedQ1OneShellExpectation

/-! The complete actual signed q1 generator expectation before panel substitution. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The source-derived affine payment, retaining the exact flat cell loss. -/
def oldSignedQ1AffineCap (M : ABKModel 2) (n : ℤ) (t b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  oldSignedQ1AffineCap' M n t b L

/-- The actual generator expectation obeys the complete signed AN bill.
All spatial, covariance, history, inverse-bank and integrability inputs are
supplied internally from the source model and the previous native states. -/
theorem old_signed_q1_generator_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    (∫ ω,nativeSourceBandMeanGenerator M h n 1 t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      oldSignedFlatBoundaryEnergy (originCube 2 n) b L+oldSignedQ1AffineCap M n t b L-
        b^2*(parentBoundaryBandInverseMean M n 1 t-2)+oldSignedQ1ErrorCap M n t b L := by
  exact old_signed_q1_generator_expectation' M h hM hg n hpast t ht

end
end ASDExplicitGamma.Native

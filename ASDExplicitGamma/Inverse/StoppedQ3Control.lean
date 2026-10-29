module

public import ASDExplicitGamma.Inverse.StoppedQ3Probability
public import ASDExplicitGamma.Inverse.StoppedQ3Independence

/-! The actual q3 application supplies every stopped-cluster mark input. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model

/-- Every mark-control input is proved on the physical cutoff sample space
from the ordinary protected native past. The only density choice is the
source's permitted upward rounding of E_b times the raw Markov budget. -/
theorem q3_mark_control (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (j : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple)
    (q : ℝ) (hq : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ j+40, nativeInductionState M h k) :
    PlanarMarkControl (Cutoff.cutoffSampleLaw M).toMeasure
      (q3PlanarMarks M j τ (waveGateEta t)) q where
  local_measurable := q3_local_mark_measurable M j τ (waveGateEta t)
  positive_measurable := q3_positive_mark_measurable M j τ (waveGateEta t)
  local_probability := fun x => (q3_local_probability_of_native M h hg j τ (waveGateEta t) hτ hpast x).trans hq
  positive_probability := q3_positive_probability_of_native M h hM hg j τ t hpast
  local_independent := by
    intro I inst x hx
    exact q3_local_marks_independent M h hM j τ (waveGateEta t) x hx
  positive_independent := by
    intro n I inst x c hx hc
    exact q3_positive_activations_independent M h hM j τ (waveGateEta t) n x c hx hc

end ASDExplicitGamma.Inverse

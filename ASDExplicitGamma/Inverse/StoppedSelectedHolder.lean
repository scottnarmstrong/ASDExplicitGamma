module

public import ASDExplicitGamma.Inverse.StoppedSelectedCandidates
public import ASDExplicitGamma.Inverse.StoppedMismatchHolder

/-! Actual selected-height Holder payment without conditioning or independence. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Holder for any observable restricted to an actual selected-height atom.
The ordinary 2p norm is retained; the atom probability is derived from q3. -/
theorem q3_selected_indicator_holder (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k) (n : ℕ)
    (X : Cutoff.CutoffSample 2 → ℝ) (hX : AEStronglyMeasurable X (Cutoff.cutoffSampleLaw A).toMeasure)
    (p : ℝ) (hp : 0 < p) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let E := {ω | q3StoppedHeight A Q H0 τ (waveGateEta t) ω=H0+12+n}
    eLpNorm (E.indicator X) (ENNReal.ofReal p) μ ≤
      eLpNorm X (ENNReal.ofReal (2*p)) μ*
        ENNReal.ofReal ((selectedTailProbability H0 n)^(1/(2*p):ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
  let E := {ω | H ω=H0+12+n}
  have hmH : Measurable H := q3_stopped_height_measurable A Q H0 τ (waveGateEta t)
  have hE : MeasurableSet E := hmH (measurableSet_singleton _)
  have hprob : μ E ≤ ENNReal.ofReal (selectedTailProbability H0 n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (q3_selected_height_atom A h hA hg Q H0 hH τ hτ t q hq0 hq hraw hpast n)
  have hr := ENNReal.rpow_le_rpow hprob (by positivity : (0:ℝ) ≤ 1/(2*p))
  rw [ENNReal.ofReal_rpow_of_pos (by unfold selectedTailProbability; positivity)] at hr
  exact (indicator_holder μ X hX E hE p hp).trans
    (mul_le_mul_of_nonneg_left hr (zero_le : (0:ℝ≥0∞) ≤ _))

end
end ASDExplicitGamma.Inverse

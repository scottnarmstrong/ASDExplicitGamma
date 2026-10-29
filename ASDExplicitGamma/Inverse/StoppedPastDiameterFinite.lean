module

public import ASDExplicitGamma.Inverse.StoppedQ3Control
public import ASDExplicitGamma.Inverse.StoppedRealDiameter

/-! Simultaneous finiteness of all actual old-label cluster fields in the
protected native past. No finiteness premise is exported to model consumers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Every actual cluster diameter field at every protected old label is
finite simultaneously almost surely, uniformly over all physical blocks. -/
theorem q3_past_diameter_ae_ne_top (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (upper : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ upper+40, nativeInductionState M h k) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ j, j ≤ upper → ∀ x,
      diameterField (q3PlanarMarks M j τ (waveGateEta t)) ω x ≠ ∞ := by
  apply ae_all_iff.mpr
  intro j
  by_cases hj : j ≤ upper
  · have hB := q3_mark_control M h hM hg j τ hτ t q hraw
      (fun k hk => hpast k (by omega))
    have hf := diameter_field_ae_ne_top (Cutoff.cutoffSampleLaw M).toMeasure
      (q3PlanarMarks M j τ (waveGateEta t)) q hB hq0 hq
    filter_upwards [hf] with ω hω
    intro _
    exact hω
  · filter_upwards with ω hω
    exact (hj hω).elim

end
end ASDExplicitGamma.Inverse

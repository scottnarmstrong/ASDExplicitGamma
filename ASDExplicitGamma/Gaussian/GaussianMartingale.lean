module

public import ASDExplicitGamma.Gaussian.IndependentMartingale
public import ASDExplicitGamma.Gaussian.SeriesHeat
public import Mathlib.Probability.Independence.InfinitePi

/-! # The actual Hilbert Gaussian partial sums form a martingale -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (v : ℕ → V)

def gaussianIncrement (n : ℕ) (ω : ℕ → ℝ) : V := ω n • v n

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] in
theorem stronglyMeasurable_gaussianIncrement (n : ℕ) : StronglyMeasurable (gaussianIncrement v n) :=
  ((continuous_apply n).smul continuous_const).stronglyMeasurable

noncomputable def gaussianFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural (gaussianIncrement v) (stronglyMeasurable_gaussianIncrement v)

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] in
theorem integrable_gaussianIncrement (n : ℕ) : Integrable (gaussianIncrement v n) standardGaussianInfinitePi := by
  have hs : Integrable (fun r : ℝ => r • v n) (gaussianReal 0 1) :=
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1) (memLp_id_gaussianReal 1)).smul_const (v n)
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).integrable_comp
    ((continuous_id.smul continuous_const).aestronglyMeasurable) |>.mpr hs

omit [MeasurableSpace V] [BorelSpace V] in
theorem integral_gaussianIncrement (n : ℕ) : ∫ ω, gaussianIncrement v n ω ∂standardGaussianInfinitePi = 0 := by
  have hmap : standardGaussianInfinitePi.map (fun ω : ℕ → ℝ => ω n) = gaussianReal 0 1 :=
    Measure.infinitePi_map_eval _ n
  have hm : AEStronglyMeasurable (fun r : ℝ => r • v n)
      (standardGaussianInfinitePi.map (fun ω : ℕ → ℝ => ω n)) := by
    rw [hmap]
    exact (continuous_id.smul continuous_const).aestronglyMeasurable
  change (∫ ω : ℕ → ℝ, ω n • v n ∂standardGaussianInfinitePi) = 0
  rw [← integral_map (φ := fun ω : ℕ → ℝ => ω n) (f := fun r : ℝ => r • v n)
    (measurable_pi_apply n).aemeasurable hm, hmap,
    integral_smul_const, integral_id_gaussianReal, zero_smul]

/-- The offset simply includes the first increment at time zero. -/
theorem gaussianPartialSum_martingale :
    Martingale (fun n ω => gaussianPartialSum v (n + 1) ω) (gaussianFiltration v)
      standardGaussianInfinitePi :=
  independent_sum_martingale standardGaussianInfinitePi (gaussianIncrement v)
    (stronglyMeasurable_gaussianIncrement v)
    (iIndepFun_infinitePi (X := fun n r => r • v n) (fun _ => by fun_prop))
    (integrable_gaussianIncrement v) (integral_gaussianIncrement v)

end
end ASDExplicitGamma.Gaussian

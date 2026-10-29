module

public import ASDExplicitGamma.Gaussian.SeriesFullLp

/-! # Gaussian norm-moment bounds pass through full Lᵖ convergence -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Continuity of the Lᵖ norm gives full-sequence convergence of all finite image moments. -/
theorem tendsto_gaussianSeries_image_lpNorm (v : ℕ → V)
    (hv : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) {p : ℝ} [Fact (2 ≤ p)] :
    Tendsto (fun N => (eLpNorm (fun ω => T (gaussianPartialSum v N ω))
      (ENNReal.ofReal p) standardGaussianInfinitePi).toReal) atTop
      (𝓝 ((eLpNorm (gaussianSeriesLimitE hv T) (ENNReal.ofReal p) standardGaussianInfinitePi).toReal)) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) Fact.out)
  have hfact : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp1⟩
  have hh := (gaussianPartialSum_image_tendsto_Lp v hv T (p := p)).norm
  simpa only [Lp.norm_toLp] using hh

/-- Uniform squared moment bounds on every orthogonal projection hold for the full actual
Gaussian image. The image's finite moments are independently provided by the H³ realization. -/
theorem gaussianSeries_image_lpNorm_sq_le (v : ℕ → V)
    (hv : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) {p C : ℝ} [Fact (2 ≤ p)]
    (hbound : ∀ N, (eLpNorm (fun ω => T (gaussianPartialSum v N ω))
      (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤ C) :
    (eLpNorm (gaussianSeriesLimitE hv T) (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤ C := by
  exact le_of_tendsto ((tendsto_gaussianSeries_image_lpNorm v hv T).pow 2)
    (Eventually.of_forall hbound)

end
end ASDExplicitGamma.Gaussian

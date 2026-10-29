module

public import ASDExplicitGamma.Gaussian.SeriesHeat

/-! # Full-sequence Lᵖ convergence of the Hilbert Gaussian series and bounded images -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

local instance instLpExponent {p : ℝ} [Fact (2 ≤ p)] : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) Fact.out)⟩

section
variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The selected a.e. fast limit is also the limit of the entire sequence in every finite Lᵖ. -/
theorem gaussianPartialSum_tendsto_Lp (v : ℕ → V) (hs : Summable (fun j => ‖v j‖ ^ 2))
    {p : ℝ} [Fact (2 ≤ p)] :
    Tendsto (fun n => (memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hs n).toLp (gaussianPartialSum v n)) atTop
      (𝓝 ((memLp_gaussianSeriesLimit v hs (Fact.out : 2 ≤ p)).toLp (gaussianSeriesLimit v hs))) := by
  obtain ⟨f, hf⟩ := exists_gaussianPartialSum_Lp_limit v hs (p := p)
  have he := ae_eq_gaussianSeriesLimit_of_Lp_limit v hs f hf
  have hfe : f = (memLp_gaussianSeriesLimit v hs (Fact.out : 2 ≤ p)).toLp (gaussianSeriesLimit v hs) := by
    apply Lp.ext
    exact he.trans (memLp_gaussianSeriesLimit v hs (Fact.out : 2 ≤ p)).coeFn_toLp.symm
  rwa [hfe] at hf

/-- Every bounded Banach image has full-sequence Lᵖ convergence, with no Gaussian convergence
assertion based on Banach squared-norm summability alone. -/
theorem gaussianPartialSum_image_tendsto_Lp (v : ℕ → V) (hs : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) {p : ℝ} [Fact (2 ≤ p)] :
    Tendsto (fun n => ((memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hs n).continuousLinearMap_comp T).toLp
      (fun ω => T (gaussianPartialSum v n ω))) atTop
      (𝓝 ((memLp_gaussianSeriesLimitE hs T (Fact.out : 2 ≤ p)).toLp (gaussianSeriesLimitE hs T))) := by
  have hh := (T.compLpL (ENNReal.ofReal p) standardGaussianInfinitePi).continuous.tendsto
    ((memLp_gaussianSeriesLimit v hs (Fact.out : 2 ≤ p)).toLp (gaussianSeriesLimit v hs))
    |>.comp (gaussianPartialSum_tendsto_Lp v hs)
  have he (f : (ℕ → ℝ) → V) (hf : MemLp f (ENNReal.ofReal p) standardGaussianInfinitePi) :
      T.compLpL (ENNReal.ofReal p) standardGaussianInfinitePi (hf.toLp f) =
        (hf.continuousLinearMap_comp T).toLp (fun ω => T (f ω)) := by
    apply Lp.ext
    filter_upwards [T.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      (hf.continuousLinearMap_comp T).coeFn_toLp] with ω h₀ h₁ h₂
    rw [h₀, h₁, h₂]
  have hseq : (T.compLpL (ENNReal.ofReal p) standardGaussianInfinitePi ∘
      fun n => (memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hs n).toLp (gaussianPartialSum v n)) =
      fun n => ((memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hs n).continuousLinearMap_comp T).toLp
        (fun ω => T (gaussianPartialSum v n ω)) := by
    funext n
    exact he _ _
  rw [hseq] at hh
  have hlim := he (gaussianSeriesLimit v hs) (memLp_gaussianSeriesLimit v hs (Fact.out : 2 ≤ p))
  rw [hlim] at hh
  exact hh

end
end ASDExplicitGamma.Gaussian

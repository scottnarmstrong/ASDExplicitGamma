module

public import ASDExplicitGamma.Gaussian.TimeAverage

/-! # Exact independent-law transfer, including finite fresh bands -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Transport a literal independent insertion to the older-law/series product. The law may
be a single shell or a whole finite band; no statement about its spatial centers is assumed. -/
theorem integral_independent_insertion {Ω V E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y ρ)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (hlaw : ρ.map Y = standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (hMom : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) (ρ.map X))
    (Φ : E → ℝ) (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) (t : ℝ) :
    Integrable (fun ω => Φ (X ω + Real.sqrt t • Y ω)) ρ ∧
      (∫ ω, Φ (X ω + Real.sqrt t • Y ω) ∂ρ) =
        ∫ p : E × (ℕ → ℝ), Φ (p.1 + Real.sqrt t • gaussianSeriesLimitE hA T p.2)
          ∂(ρ.map X).prod standardGaussianInfinitePi := by
  let Z := gaussianSeriesLimitE hA T
  let ν := ρ.map X
  let f : E × E → ℝ := fun p => Φ (p.1 + Real.sqrt t • p.2)
  have hf : Measurable f := hΦ.comp (measurable_fst.add (measurable_snd.const_smul (Real.sqrt t)))
  have hZ : Measurable Z := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hpair : ρ.map (fun ω => (X ω, Y ω)) =
      ν.prod (standardGaussianInfinitePi.map Z) := by
    rw [hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hlaw]
  have hprod : ν.prod (standardGaussianInfinitePi.map Z) =
      (ν.prod standardGaussianInfinitePi).map (Prod.map id Z) := by
    simpa only [Measure.map_id] using Measure.map_prod_map ν standardGaussianInfinitePi measurable_id hZ
  have hint := integrable_randomBaseHeatIntegrand hA T ν hMom Φ hΦ hg t
  have hfprod : Integrable f ((ν.prod standardGaussianInfinitePi).map (Prod.map id Z)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (measurable_id.prodMap hZ).aemeasurable).mpr hint
  have hfjoint : Integrable f (ρ.map (fun ω => (X ω, Y ω))) := by
    rw [hpair, hprod]
    exact hfprod
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable (hX.prodMk hY).aemeasurable).mp hfjoint, ?_⟩
  calc
    _ = ∫ p, f p ∂ρ.map (fun ω => (X ω, Y ω)) :=
      (integral_map (hX.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂(ν.prod standardGaussianInfinitePi).map (Prod.map id Z) := by rw [hpair, hprod]
    _ = _ := integral_map (measurable_id.prodMap hZ).aemeasurable hf.aestronglyMeasurable

end ASDExplicitGamma.Gaussian

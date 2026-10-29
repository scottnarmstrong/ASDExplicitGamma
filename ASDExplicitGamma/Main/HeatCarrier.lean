module

public import ASDExplicitGamma.Gaussian.ModelHeat

/-! The existing model heat adapter with its Hilbert carrier made generic.
Adapted from Gaussian.ModelHeat; no finite-rank passage is repeated. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory ProbabilityTheory Homogenization Set Filter ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

/-- Fubini transfers any measurable polynomial observable from the model product law to its
Gaussian-series realization. -/
theorem main_modelHeatAverage_eq_randomBaseHeatAverage
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Ψ : C(K, ℝ) → ℝ) (hΨ : Measurable Ψ) (hg : HasPolynomialGrowth Ψ) (t : ℝ) :
    modelHeatAverage K M m Ψ t = randomBaseHeatAverage hA T
      ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)) Ψ t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := olderField K m
  let Y := fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))
  let Z := gaussianSeriesLimitE hA T
  let ν := μ.map X
  have hX : Measurable X := measurable_olderField K ell m hK
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hZ : Measurable Z := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hjoint : μ.map (fun ω => (X ω, Y ω)) = ν.prod (standardGaussianInfinitePi.map Z) := by
    rw [← hlaw]
    exact (indepFun_olderField_freshShell K M ell m hK).map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable
  let f : C(K, ℝ) × C(K, ℝ) → ℝ := fun p => Ψ (p.1 + Real.sqrt t • p.2)
  have hf : Measurable f := hΨ.comp (measurable_fst.add (measurable_snd.const_smul (Real.sqrt t)))
  have hprod : ν.prod (standardGaussianInfinitePi.map Z) =
      (ν.prod standardGaussianInfinitePi).map (Prod.map id Z) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν standardGaussianInfinitePi measurable_id hZ
  have hint : Integrable (fun p : C(K, ℝ) × (ℕ → ℝ) => Ψ (p.1 + Real.sqrt t • Z p.2))
      (ν.prod standardGaussianInfinitePi) :=
    integrable_randomBaseHeatIntegrand hA T ν
      (integrable_polynomial_olderFieldLaw K M ell m hK) Ψ hΨ hg t
  calc
    modelHeatAverage K M m Ψ t = ∫ p, f p ∂μ.map (fun ω => (X ω, Y ω)) :=
      (integral_map (hX.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂(ν.prod standardGaussianInfinitePi).map (Prod.map id Z) := by
      rw [hjoint, hprod]
    _ = ∫ p : C(K, ℝ) × (ℕ → ℝ), Ψ (p.1 + Real.sqrt t • Z p.2)
        ∂ν.prod standardGaussianInfinitePi :=
      integral_map (measurable_id.prodMap hZ).aemeasurable hf.aestronglyMeasurable
    _ = randomBaseHeatAverage hA T ν Ψ t := integral_prod _ hint

/-- Heat differentiation on the model for any realization of its actual fresh-shell law. -/
theorem main_c1On_modelHeatAverage_of_realization
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Φ : C(K, ℝ) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
      ContinuousOn (modelHeatAverage K M m Φ) (Ici 0) ∧
      ContinuousOn (fun t => (1 / 2 : ℝ) * modelHeatTraceAverage K M m Φ
        (fun j => T (v j)) t) (Ici 0) ∧
      (∀ t ∈ Ioi 0, HasDerivAt (modelHeatAverage K M m Φ)
        ((1 / 2 : ℝ) * modelHeatTraceAverage K M m Φ (fun j => T (v j)) t) t) ∧
      HasDerivWithinAt (modelHeatAverage K M m Φ)
        ((1 / 2 : ℝ) * modelHeatTraceAverage K M m Φ (fun j => T (v j)) 0) (Ici 0) 0 := by
  have hg : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hv, _, _⟩ := hΦ
    exact ⟨C, hC, d, hv⟩
  have heq : modelHeatAverage K M m Φ =
      randomBaseHeatAverage hA T ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)) Φ := by
    funext t
    exact main_modelHeatAverage_eq_randomBaseHeatAverage K M ell m hK hA T hlaw Φ hΦ.1.continuous.measurable hg t
  have htrace : modelHeatTraceAverage K M m Φ (fun j => T (v j)) =
      randomBaseHeatTraceAverage hA T ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)) Φ := by
    funext t
    exact main_modelHeatAverage_eq_randomBaseHeatAverage K M ell m hK hA T hlaw
      (modelCovarianceTrace Φ (fun j => T (v j)))
      (measurable_modelCovarianceTrace Φ hΦ.1 _)
      (polynomial_modelCovarianceTrace _ (summable_sq_norm_gaussianDirections hA T) Φ hΦ) t
  rw [heq, htrace]
  exact c1On_randomBaseHeatAverage hA T _ (integrable_polynomial_olderFieldLaw K M ell m hK) Φ hΦ

end ASDExplicitGamma.Main

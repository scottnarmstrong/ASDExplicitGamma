module

public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Gaussian.ModelHeatResponse

/-! # Deterministic images of the model's old and fresh coefficient fields -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- A bounded deterministic map preserves all polynomial moments of a finite measure. -/
theorem polynomial_moments_map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) μ)
    (A : E →L[ℝ] F) (d : ℕ) :
    Integrable (fun x : F => (1 + ‖x‖) ^ d) (μ.map A) := by
  apply (integrable_map_measure (by fun_prop) A.continuous.measurable.aemeasurable).mpr
  apply ((hμ d).const_mul ((1 + ‖A‖) ^ d)).mono'
    (((continuous_const.add A.continuous.norm).pow d).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    have ha := A.le_opNorm x
    have hb : 1 + ‖A x‖ ≤ (1 + ‖A‖) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg A, norm_nonneg x]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖A x‖) hb d
    simpa only [Function.comp_def, Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖A x‖) ^ d), mul_pow] using hp

/-- An insertion after separate deterministic maps of the old and fresh fields. This retains
all cross covariances within each mapped field. -/
noncomputable def mappedModelAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ)
    (A B : C(K, ℝ) →L[ℝ] F) (Φ : F → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, Φ (A (olderField K m ω) +
    Real.sqrt t • B (shellFieldScalarRestriction K (ω.1 (m + 1))))
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The image insertion has exactly the independent old-law/series product expectation. -/
theorem mappedModelAverage_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → GaussianFactorL2 ℕ} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] F) (Φ : F → ℝ)
    (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) (t : ℝ) :
    mappedModelAverage K M m A B Φ t = randomBaseHeatAverage hA (B.comp T)
      (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A) Φ t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := olderField K m
  let Y := fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))
  let Z := gaussianSeriesLimitE hA T
  let ν := μ.map X
  have hX : Measurable X := measurable_olderField K ell m hK
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hZ : Measurable Z := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hjoint : μ.map (fun ω => (A (X ω), B (Y ω))) =
      (ν.map A).prod (standardGaussianInfinitePi.map (B ∘ Z)) := by
    have hi := (indepFun_olderField_freshShell K M ell m hK).comp
      A.continuous.measurable B.continuous.measurable
    have hipair := hi.map_prod_eq_prod_map_map
      (A.continuous.measurable.comp hX).aemeasurable
      (B.continuous.measurable.comp hY).aemeasurable
    change μ.map (fun ω => (A (X ω), B (Y ω))) =
      (μ.map (A ∘ X)).prod (μ.map (B ∘ Y)) at hipair
    rw [← Measure.map_map A.continuous.measurable hX,
      ← Measure.map_map B.continuous.measurable hY, hlaw,
      Measure.map_map B.continuous.measurable hZ] at hipair
    exact hipair
  let f : F × F → ℝ := fun p => Φ (p.1 + Real.sqrt t • p.2)
  have hf : Measurable f := hΦ.comp (measurable_fst.add (measurable_snd.const_smul (Real.sqrt t)))
  have hprod : (ν.map A).prod (standardGaussianInfinitePi.map (B ∘ Z)) =
      ((ν.map A).prod standardGaussianInfinitePi).map (Prod.map id (B ∘ Z)) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (ν.map A) standardGaussianInfinitePi
      measurable_id (B.continuous.measurable.comp hZ)
  have hint := integrable_randomBaseHeatIntegrand hA (B.comp T) (ν.map A)
    (polynomial_moments_map ν (integrable_polynomial_olderFieldLaw K M ell m hK) A)
    Φ hΦ hg t
  calc
    mappedModelAverage K M m A B Φ t =
        ∫ p, f p ∂μ.map (fun ω => (A (X ω), B (Y ω))) :=
      (integral_map ((A.continuous.measurable.comp hX).prodMk
        (B.continuous.measurable.comp hY)).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂((ν.map A).prod standardGaussianInfinitePi).map (Prod.map id (B ∘ Z)) := by
      rw [hjoint, hprod]
    _ = ∫ p : F × (ℕ → ℝ), Φ (p.1 + Real.sqrt t • B (Z p.2))
        ∂(ν.map A).prod standardGaussianInfinitePi :=
      integral_map (measurable_id.prodMap (B.continuous.measurable.comp hZ)).aemeasurable hf.aestronglyMeasurable
    _ = randomBaseHeatAverage hA (B.comp T) (ν.map A) Φ t := integral_prod _ hint

end ASDExplicitGamma.Gaussian

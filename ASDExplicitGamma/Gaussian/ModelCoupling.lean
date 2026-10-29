module

public import ASDExplicitGamma.Gaussian.GeneratorSplit

/-! # Coupling the exact backward identity to the completed cutoff model -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section Growth
variable {E : Type*} [NormedAddCommGroup E]

theorem polynomial_growth_add {f g : E → ℝ} (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth (fun x => f x + g x) := by
  obtain ⟨C, hC, d, hb⟩ := hf
  obtain ⟨B, hB, e, hc⟩ := hg
  refine ⟨C + B, add_nonneg hC hB, d + e, fun x => ?_⟩
  have hd : (1 + ‖x‖) ^ d ≤ (1 + ‖x‖) ^ (d + e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have he : (1 + ‖x‖) ^ e ≤ (1 + ‖x‖) ^ (d + e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  exact (abs_add_le _ _).trans ((add_le_add (hb x) (hc x)).trans (by
    nlinarith [mul_le_mul_of_nonneg_left hd hC, mul_le_mul_of_nonneg_left he hB]))

theorem polynomial_growth_const_mul {f : E → ℝ} (hf : HasPolynomialGrowth f) (a : ℝ) :
    HasPolynomialGrowth (fun x => a * f x) := by
  obtain ⟨C, hC, d, hb⟩ := hf
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, d, fun x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg a)

end Growth

/-- The backward generator remains a continuous polynomial test, without requiring third or
fourth response derivatives. -/
theorem backwardGenerator_continuous_polynomial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (H K : ℕ → E)
    (hH : Summable (fun j => ‖H j‖ ^ 2)) (hK : Summable (fun j => ‖K j‖ ^ 2)) (θ : ℝ) :
    Continuous (backwardGenerator Φ H K θ) ∧ HasPolynomialGrowth (backwardGenerator Φ H K θ) := by
  constructor
  · exact (continuous_const.mul (continuous_modelCovarianceTrace hΦ H hH)).sub
      (continuous_const.mul (continuous_modelCovarianceTrace hΦ K hK))
  · have hp := polynomial_growth_add
      (polynomial_growth_const_mul (polynomial_modelCovarianceTrace H hH Φ hΦ) (1 / 2 : ℝ))
      (polynomial_growth_const_mul (polynomial_modelCovarianceTrace K hK Φ hΦ) (-((1 + θ) / 2)))
    unfold backwardGenerator
    simpa only [neg_mul, sub_eq_add_neg] using hp

/-- The literal actual-medium expectation of an independent auxiliary backward test. -/
noncomputable def modelBackwardAverage {W X : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ)
    (P : C(K, ℝ) →L[ℝ] X) {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2))
    (S : W →L[ℝ] X) (Φ : X → ℝ) (θ t : ℝ) : ℝ :=
  mappedModelAverage K M m P P (backwardTest hB S Φ θ t) t

/-- Both actual factors retain their exact completed cutoff law. The auxiliary factor is an
independent copy, and no independence between a center and its remainder is introduced. -/
theorem modelBackwardAverage_eq {W X : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → GaussianFactorL2 ℕ} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (P : C(K, ℝ) →L[ℝ] X) {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2))
    (S : W →L[ℝ] X) {Φ : X → ℝ} (hΦcont : Continuous Φ) (hΦpoly : HasPolynomialGrowth Φ)
    (θ : ℝ) :
    modelBackwardAverage K M m P hB S Φ θ =
      backwardAverage hA (P.comp T) hB S
        (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P) Φ θ := by
  funext t
  let Z := gaussianSeriesLimitE hB S
  let a := Real.sqrt ((1 + θ) * (1 - t))
  have hZ : StronglyMeasurable Z := stronglyMeasurable_gaussianSeriesLimitE hB S
  have hm (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) standardGaussianInfinitePi := by
    have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      convert memLp_gaussianSeriesLimitE hB S (p := (d + 2 : ℕ))
        (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
      simp [ENNReal.ofReal_add]
    exact integrable_one_add_norm_pow_of_memLp hz
  have hsm := integrable_scaled_moments standardGaussianInfinitePi Z hZ hm a
  have hsc := hZ.const_smul a
  have hGcont : Continuous (backwardTest hB S Φ θ t) :=
    continuous_integral_translate standardGaussianInfinitePi (fun ω => a • Z ω) hsc hsm hΦcont
      (by obtain ⟨C, hC, d, hb⟩ := hΦpoly
          exact ⟨C, hC, d, fun x => by simpa only [Real.norm_eq_abs] using hb x⟩)
  have hGpoly : HasPolynomialGrowth (backwardTest hB S Φ θ t) :=
    polynomial_growth_integral_translate standardGaussianInfinitePi (fun ω => a • Z ω) hsm hΦpoly
  let ν := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
  have hν := polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) P
  calc
    modelBackwardAverage K M m P hB S Φ θ t =
        randomBaseHeatAverage hA (P.comp T) ν (backwardTest hB S Φ θ t) t :=
      mappedModelAverage_eq K M ell m hK hA T hlaw P P _ hGcont.measurable hGpoly t
    _ = backwardAverage hA (P.comp T) hB S ν Φ θ t :=
      (integral_prod _ (integrable_randomBaseHeatIntegrand hA (P.comp T) ν hν _ hGcont.measurable hGpoly t)).symm

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.BandModelLaw
public import ASDExplicitGamma.Gaussian.LawTransfer

/-! # Heat calculus for literal finite-band model insertions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The literal expectation after a finite fresh band, with separate old/fresh maps. -/
noncomputable def bandModelAverage {b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ) (k : Fin b → ℤ)
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, Φ (A (olderField K m ω) + Real.sqrt t • B (modelBand K k ω))
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Exact product-law transfer for a physical finite band. -/
theorem bandModelAverage_eq {b : ℕ} {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) (t : ℝ) :
    bandModelAverage K M m k A B Φ t = randomBaseHeatAverage hA (B.comp T)
      (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A) Φ t := by
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => A (olderField K m ω)
  let Y := fun ω => B (modelBand K k ω)
  have hX : Measurable X := A.continuous.measurable.comp (measurable_olderField K ell m hK)
  have hY : Measurable Y := B.continuous.measurable.comp (measurable_modelBand K k)
  have hi := (indepFun_olderField_band K M ell m hK k hk).comp
    A.continuous.measurable B.continuous.measurable
  have hmap : ρ.map Y = standardGaussianInfinitePi.map (gaussianSeriesLimitE hA (B.comp T)) := by
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map B) hlaw
    rw [Measure.map_map B.continuous.measurable (measurable_modelBand K k),
      Measure.map_map B.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable] at hh
    exact hh
  have hMom : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) (ρ.map X) := by
    rw [show ρ.map X = ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A from
      (Measure.map_map A.continuous.measurable (measurable_olderField K ell m hK)).symm]
    exact polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) A
  have hh := (integral_independent_insertion ρ X Y hX hY hi hA (B.comp T) hmap hMom Φ hΦ hg t).2
  have hint := integrable_randomBaseHeatIntegrand hA (B.comp T) (ρ.map X) hMom Φ hΦ hg t
  have heq := hh.trans (integral_prod _ hint)
  simpa only [Measure.map_map A.continuous.measurable (measurable_olderField K ell m hK),
    X, Y, ρ, bandModelAverage, randomBaseHeatAverage, gaussianSeriesHeatAverage,
    gaussianSeriesHeatArgument, Function.comp_def] using heq

/-- The heat identity for deterministic old/fresh images on the actual model law. -/
theorem c1On_bandModelAverage {b : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] F) (Φ : F → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (bandModelAverage K M m k A B Φ) (Ici 0) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * bandModelAverage K M m k A B
      (modelCovarianceTrace Φ (fun j => B (T (v j)))) t) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (bandModelAverage K M m k A B Φ)
      ((1 / 2 : ℝ) * bandModelAverage K M m k A B
        (modelCovarianceTrace Φ (fun j => B (T (v j)))) t) t) ∧
    HasDerivWithinAt (bandModelAverage K M m k A B Φ)
      ((1 / 2 : ℝ) * bandModelAverage K M m k A B
        (modelCovarianceTrace Φ (fun j => B (T (v j)))) 0) (Ici 0) 0 := by
  let ν := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A)
  have hm := polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) A
  have hg : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hv, _, _⟩ := hΦ
    exact ⟨C, hC, d, hv⟩
  have heq : bandModelAverage K M m k A B Φ = randomBaseHeatAverage hA (B.comp T) ν Φ := by
    funext t
    exact bandModelAverage_eq K M ell m hK k hk hA T hlaw A B Φ hΦ.1.continuous.measurable hg t
  have htrace : bandModelAverage K M m k A B
      (modelCovarianceTrace Φ (fun j => B (T (v j)))) = randomBaseHeatTraceAverage hA (B.comp T) ν Φ := by
    funext t
    exact bandModelAverage_eq K M ell m hK k hk hA T hlaw A B _
      (measurable_modelCovarianceTrace Φ hΦ.1 _)
      (polynomial_modelCovarianceTrace _ (summable_sq_norm_gaussianDirections hA (B.comp T)) Φ hΦ) t
  rw [heq, htrace]
  exact c1On_randomBaseHeatAverage hA (B.comp T) ν hm Φ hΦ

/-- The moment identity holds on the actual model for every finite real `p ≥ 2`. -/
theorem c1On_bandModelPowerAverage {b : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] F)
    (Φ : F → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ x, 0 ≤ Φ x) {p : ℝ} (hp : 2 ≤ p) :
    ContinuousOn (bandModelAverage K M m k A B (fun x => Φ x ^ p)) (Ici 0) ∧
    ContinuousOn (bandModelAverage K M m k A B (modelPowerHeatGenerator Φ (fun j => B (T (v j))) p)) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (bandModelAverage K M m k A B (fun x => Φ x ^ p))
      (bandModelAverage K M m k A B (modelPowerHeatGenerator Φ (fun j => B (T (v j))) p) t) t) ∧
    HasDerivWithinAt (bandModelAverage K M m k A B (fun x => Φ x ^ p))
      (bandModelAverage K M m k A B (modelPowerHeatGenerator Φ (fun j => B (T (v j))) p) 0) (Ici 0) 0 := by
  have hbase := c1On_bandModelAverage K M ell m hK k hk hA T hlaw A B
    (fun x => Φ x ^ p) (hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦnonneg hp)
  have heq : (fun t => (1 / 2 : ℝ) * bandModelAverage K M m k A B
      (modelCovarianceTrace (fun x => Φ x ^ p) (fun j => B (T (v j)))) t) =
      bandModelAverage K M m k A B (modelPowerHeatGenerator Φ (fun j => B (T (v j))) p) := by
    funext t
    unfold bandModelAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => modelCovarianceTrace_rpow hA (B.comp T) Φ hΦ hΦnonneg hp _
  refine ⟨hbase.1, ?_, ?_, ?_⟩
  · rw [← heq]
    exact hbase.2.1
  · intro t ht
    simpa only [congrFun heq t] using hbase.2.2.1 t ht
  · simpa only [congrFun heq 0] using hbase.2.2.2

end ASDExplicitGamma.Gaussian

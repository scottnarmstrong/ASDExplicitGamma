module

public import ASDExplicitGamma.Gaussian.ModelHeat

/-! # Real moment powers in the model Gaussian heat identity -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The carré-du-champ trace in physical coefficient directions. -/
noncomputable def modelGradientSquareTrace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Φ : E → ℝ) (H : ℕ → E) (x : E) : ℝ :=
  ∑' j, (fderiv ℝ Φ x (H j)) ^ 2

/-- The two-term moment generator (1.12), including the factor one half. -/
noncomputable def modelPowerHeatGenerator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Φ : E → ℝ) (H : ℕ → E) (p : ℝ) (x : E) : ℝ :=
  p * Φ x ^ (p - 1) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ H x) +
    (p * (p - 1) / 2) * Φ x ^ (p - 2) * modelGradientSquareTrace Φ H x

/-- The infinite trace obeys the real power rule at every coefficient, including zeros. -/
theorem modelCovarianceTrace_rpow
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ x, 0 ≤ Φ x) {p : ℝ} (hp : 2 ≤ p) (x : E) :
    (1 / 2 : ℝ) * modelCovarianceTrace (fun y => Φ y ^ p) (fun j => T (v j)) x =
      modelPowerHeatGenerator Φ (fun j => T (v j)) p x := by
  have heq := gaussianSeriesHeatTrace_rpow hA T Φ hΦ hΦnonneg hp x 0 (fun _ => 0)
  have heq' : modelCovarianceTrace (fun y => Φ y ^ p) (fun j => T (v j)) x =
      p * Φ x ^ (p - 1) * modelCovarianceTrace Φ (fun j => T (v j)) x +
        p * (p - 1) * Φ x ^ (p - 2) * modelGradientSquareTrace Φ (fun j => T (v j)) x := by
    simpa only [gaussianSeriesHeatTrace, gaussianSeriesPowerHessianTrace,
      gaussianSeriesPowerGradientSquareTrace, gaussianSeriesHeatArgument, Real.sqrt_zero,
      zero_smul, add_zero, modelCovarianceTrace, modelGradientSquareTrace] using heq
  rw [heq', modelPowerHeatGenerator]
  ring

/-- The moment identity holds on the actual model for every finite real `p ≥ 2`. -/
theorem c1On_modelPowerHeatAverage_of_realization
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → GaussianFactorL2 ℕ} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Φ : C(K, ℝ) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ x, 0 ≤ Φ x) {p : ℝ} (hp : 2 ≤ p) :
    ContinuousOn (modelHeatAverage K M m (fun x => Φ x ^ p)) (Ici 0) ∧
    ContinuousOn (modelHeatAverage K M m (modelPowerHeatGenerator Φ (fun j => T (v j)) p)) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (modelHeatAverage K M m (fun x => Φ x ^ p))
      (modelHeatAverage K M m (modelPowerHeatGenerator Φ (fun j => T (v j)) p) t) t) ∧
    HasDerivWithinAt (modelHeatAverage K M m (fun x => Φ x ^ p))
      (modelHeatAverage K M m (modelPowerHeatGenerator Φ (fun j => T (v j)) p) 0) (Ici 0) 0 := by
  have hbase := c1On_modelHeatAverage_of_realization K M ell m hK hA T hlaw
    (fun x => Φ x ^ p) (hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦnonneg hp)
  have heq : (fun t => (1 / 2 : ℝ) *
      modelHeatTraceAverage K M m (fun x => Φ x ^ p) (fun j => T (v j)) t) =
      modelHeatAverage K M m (modelPowerHeatGenerator Φ (fun j => T (v j)) p) := by
    funext t
    rw [modelHeatTraceAverage, modelHeatAverage, modelHeatAverage, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => modelCovarianceTrace_rpow hA T Φ hΦ hΦnonneg hp _
  refine ⟨hbase.1, ?_, ?_, ?_⟩
  · rw [← heq]
    exact hbase.2.1
  · intro t ht
    simpa only [congrFun heq t] using hbase.2.2.1 t ht
  · simpa only [congrFun heq 0] using hbase.2.2.2

end ASDExplicitGamma.Gaussian

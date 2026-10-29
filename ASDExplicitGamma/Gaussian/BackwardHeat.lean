module

public import ASDExplicitGamma.Gaussian.BackwardTest
public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! # GA-BACKWARD-HEAT: independent auxiliary Gaussian interpolation -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {V W E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (P : V →L[ℝ] E)
  {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2)) (S : W →L[ℝ] E)
  (ν : Measure E) [IsFiniteMeasure ν]

/-- The auxiliary vector alone is independent of the actual older/fresh medium. -/
noncomputable def backwardAverage (Φ : E → ℝ) (θ : ℝ) : ℝ → ℝ :=
  timeHeatAverage hA P ν (backwardTest hB S Φ θ)

/-- The exact generator difference (8.15). -/
noncomputable def backwardGenerator (Φ : E → ℝ) (H K : ℕ → E) (θ : ℝ) (x : E) : ℝ :=
  (1 / 2 : ℝ) * modelCovarianceTrace Φ H x -
    ((1 + θ) / 2) * modelCovarianceTrace Φ K x

include hA in
omit [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology E] in
/-- Moving a full covariance contraction through the auxiliary average is justified by its
bounded trace functional and the C² polynomial bounds. -/
theorem backwardTest_covarianceTrace {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (θ t : ℝ) (x : E) :
    modelCovarianceTrace (backwardTest hB S Φ θ t) (fun j => P (v j)) x =
      gaussianSeriesHeatAverage hB S (modelCovarianceTrace Φ (fun j => P (v j))) x
        ((1 + θ) * (1 - t)) := by
  let Z := gaussianSeriesLimitE hB S
  have hMom (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) standardGaussianInfinitePi := by
    have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      convert memLp_gaussianSeriesLimitE hB S (p := (d + 2 : ℕ))
        (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
      simp [ENNReal.ofReal_add]
    exact integrable_one_add_norm_pow_of_memLp hz
  exact covarianceTrace_integral_translate (fun j => P (v j))
    (summable_sq_norm_gaussianDirections hA P) standardGaussianInfinitePi
    (fun ω => Real.sqrt ((1 + θ) * (1 - t)) • Z ω)
    ((stronglyMeasurable_gaussianSeriesLimitE hB S).const_smul _)
    (integrable_scaled_moments standardGaussianInfinitePi Z
      (stronglyMeasurable_gaussianSeriesLimitE hB S) hMom _) hΦ x

/-- The expected derivative is exactly the difference of actual and auxiliary generators,
with all directions retained, including singular and off-diagonal center covariances. -/
theorem backward_derivative_eq {Φ : E → ℝ}
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) {θ : ℝ} (hθ : 0 < θ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    timeHeatDerivative hA P ν (backwardTest hB S Φ θ) (backwardTestDerivative hB S Φ θ) t =
      backwardAverage hA P hB S ν (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) θ t := by
  let G := backwardTest hB S Φ θ
  let D := backwardTestDerivative hB S Φ θ
  let μ := ν.prod standardGaussianInfinitePi
  let X : E × (ℕ → ℝ) → E := fun p => p.1 + Real.sqrt t • gaussianSeriesLimitE hA P p.2
  let HA := fun j => P (v j)
  let HB := fun j => S (w j)
  have hHA := summable_sq_norm_gaussianDirections hA P
  have hHB := summable_sq_norm_gaussianDirections hB S
  have hG := backwardTest_regularity hB S hΦ hθ
  have hDcont : Continuous (D t) := hG.continuous_time.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  have hDgrowth : HasPolynomialGrowth (D t) := by
    obtain ⟨C, hC, d, hb⟩ := hG.polynomial_bound
    refine ⟨C, hC, d, fun x => ?_⟩
    have h := hb t ht x
    linarith [abs_nonneg (G t x), norm_nonneg (fderiv ℝ (G t) x), norm_nonneg (fderiv ℝ (fderiv ℝ (G t)) x)]
  have hDint := integrable_randomBaseHeatIntegrand hA P ν hν (D t) hDcont.measurable hDgrowth t
  have hTgrowth := polynomial_modelCovarianceTrace HA hHA (G t) (hG.field_growth ht)
  have hTint := integrable_randomBaseHeatIntegrand hA P ν hν (modelCovarianceTrace (G t) HA)
    (measurable_modelCovarianceTrace (G t) (hG.field_c2 t ht) HA) hTgrowth t
  have hTprod : randomBaseHeatTraceAverage hA P ν (G t) t =
      ∫ p, modelCovarianceTrace (G t) HA (X p) ∂μ := (integral_prod _ hTint).symm
  have hpoint (x : E) :
      gaussianSeriesHeatAverage hB S (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) x ((1 + θ) * (1 - t)) =
        D t x + (1 / 2 : ℝ) * modelCovarianceTrace (G t) HA x := by
    let Z := gaussianSeriesLimitE hB S
    have hMom (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) standardGaussianInfinitePi := by
      have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
        convert memLp_gaussianSeriesLimitE hB S (p := (d + 2 : ℕ))
          (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
        simp [ENNReal.ofReal_add]
      exact integrable_one_add_norm_pow_of_memLp hz
    let a := Real.sqrt ((1 + θ) * (1 - t))
    have hZm := (stronglyMeasurable_gaussianSeriesLimitE hB S).const_smul a
    have hm := integrable_scaled_moments standardGaussianInfinitePi Z
      (stronglyMeasurable_gaussianSeriesLimitE hB S) hMom a
    have hCA := polynomial_modelCovarianceTrace HA hHA Φ hΦ
    have hCB := polynomial_modelCovarianceTrace HB hHB Φ hΦ
    obtain ⟨CA, hCA0, dA, hbA⟩ := hCA
    obtain ⟨CB, hCB0, dB, hbB⟩ := hCB
    have hiA := integrable_polynomial_translate standardGaussianInfinitePi (fun ω => a • Z ω) hZm hm
      (continuous_modelCovarianceTrace hΦ HA hHA)
      ⟨CA, hCA0, dA, fun y => by simpa only [Real.norm_eq_abs] using hbA y⟩ x
    have hiB := integrable_polynomial_translate standardGaussianInfinitePi (fun ω => a • Z ω) hZm hm
      (continuous_modelCovarianceTrace hΦ HB hHB)
      ⟨CB, hCB0, dB, fun y => by simpa only [Real.norm_eq_abs] using hbB y⟩ x
    rw [backwardTest_covarianceTrace hA P hB S hΦ θ t x]
    unfold gaussianSeriesHeatAverage
    simp only [backwardGenerator]
    change (∫ ω, (1 / 2 : ℝ) * modelCovarianceTrace Φ HA (x + a • Z ω) -
      ((1 + θ) / 2) * modelCovarianceTrace Φ HB (x + a • Z ω) ∂standardGaussianInfinitePi) =
        D t x + (1 / 2 : ℝ) * ∫ ω, modelCovarianceTrace Φ HA (x + a • Z ω) ∂standardGaussianInfinitePi
    rw [integral_sub (hiA.const_mul _) (hiB.const_mul _), integral_const_mul, integral_const_mul]
    change _ = -((1 + θ) / 2) *
      (∫ ω, modelCovarianceTrace Φ HB (x + a • Z ω) ∂standardGaussianInfinitePi) + _
    ring
  unfold timeHeatDerivative
  rw [hTprod, ← integral_const_mul]
  rw [← integral_add hDint (hTint.const_mul (1 / 2 : ℝ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => (hpoint (X p)).symm

/-- The generator-difference identity is C¹ on the closed insertion interval, with the exact negative auxiliary
coefficient and both one-sided endpoint derivatives. -/
theorem c1On_backwardAverage {Φ : E → ℝ}
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) {θ : ℝ} (hθ : 0 < θ) :
    ContinuousOn (backwardAverage hA P hB S ν Φ θ) (Icc 0 1) ∧
    ContinuousOn (backwardAverage hA P hB S ν (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) θ) (Icc 0 1) ∧
    (∀ t ∈ Ioo 0 1, HasDerivAt (backwardAverage hA P hB S ν Φ θ)
      (backwardAverage hA P hB S ν (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) θ t) t) ∧
    HasDerivWithinAt (backwardAverage hA P hB S ν Φ θ)
      (backwardAverage hA P hB S ν (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) θ 0) (Icc 0 1) 0 ∧
    HasDerivWithinAt (backwardAverage hA P hB S ν Φ θ)
      (backwardAverage hA P hB S ν (backwardGenerator Φ (fun j => P (v j)) (fun j => S (w j)) θ) θ 1) (Icc 0 1) 1 := by
  have h := c1On_timeHeatAverage hA P ν hν (backwardTest_regularity hB S hΦ hθ)
  have heq := fun {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) =>
    backward_derivative_eq hA P hB S ν hν hΦ hθ ht
  refine ⟨h.1, h.2.1.congr (fun t ht => (heq ht).symm), ?_, ?_, ?_⟩
  · intro t ht
    rw [← heq ⟨ht.1.le, ht.2.le⟩]
    exact h.2.2.1 t ht
  · rw [← heq ⟨le_refl _, zero_le_one⟩]
    exact h.2.2.2.1
  · rw [← heq ⟨zero_le_one, le_refl _⟩]
    exact h.2.2.2.2

end
end ASDExplicitGamma.Gaussian

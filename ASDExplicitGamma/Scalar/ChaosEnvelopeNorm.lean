module

public import ASDExplicitGamma.Scalar.ChaosEnvelopeMoment
public import ASDExplicitGamma.Scalar.ChaosInterpolation
public import ASDExplicitGamma.Numerics.Scalar.Readable

/-! The corrected SC-CHAOS-MOMENT-BOUND for genuine finite Gaussian Hilbert envelopes.
All second-chaos moment hypotheses of the generic interpolation lemma are discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Real nonnegative second-moment interpolation, with the probability expectation retained. -/
theorem chaos_norm_of_real_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ x, 0 ≤ Y x)
    (hY1 : Integrable Y μ) (hY2 : Integrable (fun x => (Y x)^2) μ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℝ) (hp : 2 ≤ p)
    (hbound : (∫ x, (Y x)^2 ∂μ) ≤ C^2*(∫ x, Y x ∂μ)^2) :
    eLpNorm Y (ENNReal.ofReal (p/(p-1))) μ ≤ ENNReal.ofReal (C^(2/p)*(∫ x, Y x ∂μ)) := by
  have hlin : (∫⁻ x, ENNReal.ofReal (Y x) ∂μ) = ENNReal.ofReal (∫ x, Y x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hY1 (Filter.Eventually.of_forall hY0)).symm
  have hlin2 : (∫⁻ x, (ENNReal.ofReal (Y x))^2 ∂μ) = ENNReal.ofReal (∫ x, (Y x)^2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hY2 (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    apply lintegral_congr_ae
    filter_upwards with x
    exact (ENNReal.ofReal_pow (hY0 x) 2).symm
  have hm : (∫⁻ x, (ENNReal.ofReal (Y x))^2 ∂μ) ≤
      (ENNReal.ofReal C)^2*(∫⁻ x, ENNReal.ofReal (Y x) ∂μ)^2 := by
    rw [hlin2,hlin,← ENNReal.ofReal_pow hC 2,← ENNReal.ofReal_pow (integral_nonneg hY0) 2,
      ← ENNReal.ofReal_mul (sq_nonneg C)]
    exact ENNReal.ofReal_le_ofReal hbound
  have h := chaos_conjugate_bound_of_second_moment μ (fun x => ENNReal.ofReal (Y x)) hY.ennreal_ofReal
    (ENNReal.ofReal C) p hp hm
  have he : eLpNorm Y (ENNReal.ofReal (p/(p-1))) μ =
      eLpNorm (fun x => ENNReal.ofReal (Y x)) (ENNReal.ofReal (p/(p-1))) μ := by
    have hefun : (fun x => ENNReal.ofReal (Y x)) = fun x => ‖Y x‖ₑ := by
      funext x
      exact (Real.enorm_eq_ofReal (hY0 x)).symm
    rw [hefun,eLpNorm_enorm _ hY.aestronglyMeasurable]
  rw [← he,hlin] at h
  rw [ENNReal.ofReal_rpow_of_nonneg hC (by positivity : (0:ℝ) ≤ 2/p),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)] at h
  exact h

/-- Correct q=p/(p−1) bound: the finite Gaussian Hilbert-envelope source moment is proved above. -/
theorem finite_gaussian_envelope_conjugate_bound {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (finiteGaussianEnvelope m A) (ENNReal.ofReal (p/(p-1)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1+Real.sqrt 15)^(2/p)*
        (∫ x, finiteGaussianEnvelope m A x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hc : Continuous (finiteGaussianEnvelope m A) := by
    change Continuous (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, (m i+centeredGaussianQuadratic (A i) x)^2)
    unfold centeredGaussianQuadratic
    fun_prop
  exact chaos_norm_of_real_second_moment _ _ hc.measurable (finite_gaussian_envelope_nonneg m A)
    (finite_gaussian_envelope_mean m A hA).1 (finite_gaussian_envelope_second_moment m A hA).1
    _ chaos_envelope_constants.1.le p hp (finite_gaussian_envelope_second_moment m A hA).2

end ASDExplicitGamma.Scalar

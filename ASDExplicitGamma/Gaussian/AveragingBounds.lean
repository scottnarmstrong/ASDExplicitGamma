module

public import ASDExplicitGamma.Gaussian.C2Averaging
public import ASDExplicitGamma.Gaussian.ScaledAveraging

/-! # Uniform polynomial bounds for auxiliary averages and covariance traces -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- A deterministic scalar multiple of a field with every polynomial moment has the same property. -/
theorem integrable_scaled_moments {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → E) (hZ : StronglyMeasurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ) (a : ℝ) (d : ℕ) :
    Integrable (fun ω => (1 + ‖a • Z ω‖) ^ d) μ := by
  apply ((hMom d).const_mul ((1 + |a|) ^ d)).mono'
    ((stronglyMeasurable_const.add (hZ.const_smul a).norm).pow d).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have hb : 1 + ‖a • Z ω‖ ≤ (1 + |a|) * (1 + ‖Z ω‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg a, norm_nonneg (Z ω)]
    simpa only [Pi.pow_apply, Pi.add_apply, Pi.smul_apply, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖a • Z ω‖) ^ d), mul_pow] using
      pow_le_pow_left₀ (by positivity) hb d

/-- A common polynomial bound for an auxiliary average, uniform over bounded amplitudes. -/
theorem norm_integral_scaled_translate_le
    {E Y Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → E)
    {d : ℕ} (hMom : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → Y} {C R a : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ d) (ha : |a| ≤ R) (x : E) :
    ‖∫ ω, f (x + a • Z ω) ∂μ‖ ≤
      (C * (1 + R) ^ d * ∫ ω, (1 + ‖Z ω‖) ^ d ∂μ) * (1 + ‖x‖) ^ d := by
  have hb : ∀ ω, ‖f (x + a • Z ω)‖ ≤
      (C * (1 + R) ^ d * (1 + ‖x‖) ^ d) * (1 + ‖Z ω‖) ^ d := by
    intro ω
    have htri := norm_add_le x (a • Z ω)
    rw [norm_smul, Real.norm_eq_abs] at htri
    have hm := mul_le_mul_of_nonneg_right ha (norm_nonneg (Z ω))
    have harg : 1 + ‖x + a • Z ω‖ ≤ (1 + R) * (1 + ‖x‖) * (1 + ‖Z ω‖) := by
      nlinarith [norm_nonneg x, norm_nonneg (Z ω), mul_nonneg (norm_nonneg x) (norm_nonneg (Z ω)),
        mul_nonneg hR (mul_nonneg (norm_nonneg x) (norm_nonneg (Z ω)))]
    exact (hf _).trans (by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg d) hC
      simpa only [mul_pow, mul_assoc] using hh)
  have hi := norm_integral_le_of_norm_le
    (hMom.const_mul (C * (1 + R) ^ d * (1 + ‖x‖) ^ d)) (Eventually.of_forall hb)
  simpa only [integral_const_mul, mul_assoc, mul_left_comm, mul_comm] using hi

/-- A square-summable covariance factor has a continuous Hessian trace. -/
theorem continuous_modelCovarianceTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f)
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2)) :
    Continuous (modelCovarianceTrace f H) := by
  obtain ⟨C, hC, d, hb⟩ := hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hf
  apply continuous_iff_continuousAt.mpr
  intro x
  have hdom : Summable (fun j => C * (2 + ‖x‖) ^ d * ‖H j‖ ^ 2) := hH.mul_left _
  apply tendsto_tsum_of_dominated_convergence hdom
    (fun j => (continuous_secondDirectionalDerivative hf.1 (H j)).continuousAt) ?_
  filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < 1 by norm_num)] with y hy j
  have hdist : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hnorm : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (y - x) x
  have harg : 1 + ‖y‖ ≤ 2 + ‖x‖ := by linarith
  exact (hb y (H j)).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg d) hC) (sq_nonneg _))

/-- A continuous polynomial test is integrable after a deterministic translate. -/
theorem integrable_polynomial_translate {E Y Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → E) (hZ : StronglyMeasurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → Y} (hf : Continuous f)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ d) (x : E) :
    Integrable (fun ω => f (x + Z ω)) μ := by
  obtain ⟨C, hC, d, hb⟩ := hg
  apply ((hMom d).const_mul (C * (2 + ‖x‖) ^ d)).mono'
    (hf.comp_stronglyMeasurable (stronglyMeasurable_const.add hZ)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have htri := norm_add_le x (Z ω)
    have harg : 1 + ‖x + Z ω‖ ≤ (2 + ‖x‖) * (1 + ‖Z ω‖) := by
      nlinarith [norm_nonneg x, norm_nonneg (Z ω), mul_nonneg (norm_nonneg x) (norm_nonneg (Z ω))]
    exact (hb _).trans (by
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg d) hC
      simpa only [Pi.add_apply, mul_pow, mul_assoc] using h)

/-- Independent translation averaging preserves polynomial growth. -/
theorem polynomial_growth_integral_translate {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → E)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → ℝ} (hg : HasPolynomialGrowth f) :
    HasPolynomialGrowth (fun x => ∫ ω, f (x + Z ω) ∂μ) := by
  obtain ⟨C, hC, d, hb⟩ := hg
  let K := C * (1 + (1 : ℝ)) ^ d * ∫ ω, (1 + ‖Z ω‖) ^ d ∂μ
  have hK : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun ω => pow_nonneg (by positivity) _)
  refine ⟨K, hK, d, fun x => ?_⟩
  have h := norm_integral_scaled_translate_le μ Z (f := f) (hMom d) hC
    (show (0 : ℝ) ≤ 1 by norm_num) (fun x => by simpa only [Real.norm_eq_abs] using hb x)
    (show |(1 : ℝ)| ≤ 1 by norm_num) x
  simpa only [one_smul, Real.norm_eq_abs, K] using h

end ASDExplicitGamma.Gaussian

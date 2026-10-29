module

public import ASDExplicitGamma.Inverse.HistoryPopulation

/-! The exact finite-candidate population cost at every real source moment order. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- Exact moment formula for a nonnegative extended field at any finite real order. -/
theorem nonnegative_Lp_moment_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) (p : ℝ) (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ ω, (f ω)^p ∂μ)^(1/p:ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le,enorm_eq_self]

/-- Raising the real-order norm recovers exactly the moment. -/
theorem nonnegative_Lp_moment_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) (p : ℝ) (hp : 0 < p) :
    (eLpNorm f (ENNReal.ofReal p) μ)^p = ∫⁻ ω, (f ω)^p ∂μ := by
  rw [nonnegative_Lp_moment_formula μ f hf p hp,one_div,
    ENNReal.rpow_inv_rpow hp.ne']

/-- A finite maximum costs exactly card(s)^(1/p), without any independence
between the candidates or between their selection and their values. -/
theorem finite_maximum_Lp {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset I) (f : I → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (p : ℝ) (hp : 0 < p) (B : ℝ≥0∞) (hB : ∀ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm (historyFiniteMax s f) (ENNReal.ofReal p) μ ≤ (s.card:ℝ≥0∞)^(1/p:ℝ)*B := by
  have hpoint (ω : Ω) : (historyFiniteMax s f ω)^p ≤ ∑ i ∈ s, (f i ω)^p := by
    rw [historyFiniteMax,Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0∞ => x^p)
      (fun _ _ h => ENNReal.rpow_le_rpow h hp.le) (ENNReal.zero_rpow_of_pos hp)]
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (fun _ _ => zero_le) hi
  have hmoment : (∫⁻ ω, (historyFiniteMax s f ω)^p ∂μ) ≤ (s.card:ℝ≥0∞)*B^p := by
    calc
      _ ≤ ∫⁻ ω, ∑ i ∈ s, (f i ω)^p ∂μ := lintegral_mono hpoint
      _ = ∑ i ∈ s, ∫⁻ ω, (f i ω)^p ∂μ := lintegral_finsetSum _ (fun i _ => ENNReal.continuous_rpow_const.measurable.comp (hf i))
      _ ≤ ∑ _i ∈ s, B^p := Finset.sum_le_sum (fun i hi => by
        rw [← nonnegative_Lp_moment_power μ (f i) (hf i) p hp]
        exact ENNReal.rpow_le_rpow (hB i hi) hp.le)
      _ = (s.card:ℝ≥0∞)*B^p := by simp only [Finset.sum_const,nsmul_eq_mul]
  rw [nonnegative_Lp_moment_formula μ _ (history_finite_max_measurable s f hf) p hp]
  have hh := ENNReal.rpow_le_rpow hmoment (by positivity : (0:ℝ) ≤ 1/p)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),one_div,ENNReal.rpow_rpow_inv hp.ne'] at hh
  simpa only [one_div] using! hh

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Gaussian.RioHolder

/-! # One-sided real moments from an exponential moment -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The optimized power/exponential comparison, including the negative half-line. -/
theorem positivePart_rpow_le_exp {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (x : ℝ) :
    (max x 0) ^ p ≤ c ^ p * Real.exp ((p / c) * x - p) := by
  by_cases hx : 0 < x
  · rw [max_eq_left hx.le, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hc, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos hx hc)) hp.le
    rw [Real.log_div hx.ne' hc.ne'] at hh
    have he : (x / c - 1) * p = (p / c) * x - p := by ring
    rw [he] at hh
    linarith only [hh]
  · rw [max_eq_right (le_of_not_gt hx), Real.zero_rpow hp.ne']
    exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.exp_pos _).le

/-- A single optimized exponential moment controls the full real Lᵖ norm of the positive part.
The function is proved to belong to Lᵖ as part of the conclusion. -/
theorem positivePart_lpNorm_sq_le_of_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {p c : ℝ} (hp : 0 < p) (hc : 0 < c)
    (hX : AEStronglyMeasurable X μ)
    (hexp : Integrable (fun ω => Real.exp ((p / c) * X ω)) μ)
    (hbound : (∫ ω, Real.exp ((p / c) * X ω) ∂μ) ≤ Real.exp p) :
    MemLp (fun ω => max (X ω) 0) (ENNReal.ofReal p) μ ∧
      (eLpNorm (fun ω => max (X ω) 0) (ENNReal.ofReal p) μ).toReal ^ 2 ≤ c ^ 2 := by
  let f : Ω → ℝ := fun ω => max (X ω) 0
  have hf0 (ω : Ω) : 0 ≤ f ω := le_max_right _ _
  have hfm : AEStronglyMeasurable f μ := continuous_max.comp_aestronglyMeasurable (hX.prodMk aestronglyMeasurable_const)
  have hmajor : Integrable (fun ω => c ^ p * Real.exp (-p) * Real.exp ((p / c) * X ω)) μ :=
    hexp.const_mul _
  have hle (ω : Ω) : f ω ^ p ≤ c ^ p * Real.exp (-p) * Real.exp ((p / c) * X ω) := by
    simpa only [f, sub_eq_add_neg, Real.exp_add, mul_assoc, mul_comm (Real.exp (-p))] using
      positivePart_rpow_le_exp hp hc (X ω)
  have hfi : Integrable (fun ω => f ω ^ p) μ := by
    refine hmajor.mono' ((Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable hfm) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf0 ω) p)]
    exact hle ω
  have hmem : MemLp f (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hfm (by positivity) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hf0 _)] using hfi
  refine ⟨hmem, ?_⟩
  have hm : rioMoment μ p f ≤ c ^ p := by
    have he : rioMoment μ p f = ∫ ω, f ω ^ p ∂μ := by
      unfold rioMoment
      simp only [abs_of_nonneg (hf0 _)]
    rw [he]
    calc
      _ ≤ ∫ ω, c ^ p * Real.exp (-p) * Real.exp ((p / c) * X ω) ∂μ :=
        integral_mono hfi hmajor hle
      _ = c ^ p * Real.exp (-p) * ∫ ω, Real.exp ((p / c) * X ω) ∂μ := integral_const_mul _ _
      _ ≤ c ^ p * Real.exp (-p) * Real.exp p :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = c ^ p := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [rio_lpNorm_sq hp hmem]
  calc
    _ ≤ (c ^ p) ^ (2 / p) := Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hm (by positivity)
    _ = c ^ 2 := by rw [← Real.rpow_mul hc.le, mul_div_cancel₀ _ hp.ne', Real.rpow_two]

end ASDExplicitGamma.Gaussian

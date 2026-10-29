module

public import ASDExplicitGamma.Gaussian.TwoParameter

/-! # Smooth polynomial tests under independent averaging -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {E Y Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Ω] (μ : Measure Ω)
  (Z : Ω → E) (hZ : StronglyMeasurable Z)
  (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)

omit [NormedSpace ℝ E] in
private theorem translate_polynomial_bound (x y z : E) (hy : y ∈ Metric.ball x 1) :
    1 + ‖y + z‖ ≤ (2 + ‖x‖) * (1 + ‖z‖) := by
  have hxy : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hyx := norm_sub_le y x
  have htri := norm_add_le y z
  have hnorm : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y - x) x
  nlinarith [norm_nonneg x, norm_nonneg z, mul_nonneg (norm_nonneg x) (norm_nonneg z)]

include hZ hMom in
/-- Differentiation of an independently averaged translate, with an integrable local bound
on the full Fréchet derivative. -/
theorem hasFDerivAt_integral_translate {f : E → Y} (hf : ContDiff ℝ 1 f)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x,
      ‖f x‖ + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ d) (x : E) :
    HasFDerivAt (fun y => ∫ ω, f (y + Z ω) ∂μ)
      (∫ ω, fderiv ℝ f (x + Z ω) ∂μ) x := by
  obtain ⟨C, hC, d, hb⟩ := hg
  let bound : Ω → ℝ := fun ω => C * (2 + ‖x‖) ^ d * (1 + ‖Z ω‖) ^ d
  have hi : Integrable bound μ := (hMom d).const_mul (C * (2 + ‖x‖) ^ d)
  have harg (y : E) : StronglyMeasurable (fun ω => y + Z ω) := stronglyMeasurable_const.add hZ
  have hfmeas (y : E) : StronglyMeasurable (fun ω => f (y + Z ω)) :=
    hf.continuous.comp_stronglyMeasurable (harg y)
  have hdmeas (y : E) : StronglyMeasurable (fun ω => fderiv ℝ f (y + Z ω)) :=
    (hf.continuous_fderiv (by norm_num)).comp_stronglyMeasurable (harg y)
  have hbound (y : E) (hy : y ∈ Metric.ball x 1) (ω : Ω) :
      ‖f (y + Z ω)‖ + ‖fderiv ℝ f (y + Z ω)‖ ≤ bound ω := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (translate_polynomial_bound x y (Z ω) hy) d) hC
    exact (hb _).trans (by simpa only [Pi.add_apply, id_eq, mul_pow, mul_assoc, bound] using hp)
  have hFint : Integrable (fun ω => f (x + Z ω)) μ :=
    hi.mono' (hfmeas x).aestronglyMeasurable (Eventually.of_forall fun ω => by
      have h := hbound x (Metric.mem_ball_self (by norm_num)) ω
      linarith [norm_nonneg (fderiv ℝ f (x + Z ω))])
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y ω => f (y + Z ω)) (F' := fun y ω => fderiv ℝ f (y + Z ω))
    (bound := bound) (Metric.ball_mem_nhds x (show (0 : ℝ) < 1 by norm_num))
    (Eventually.of_forall fun y => (hfmeas y).aestronglyMeasurable)
    hFint (hdmeas x).aestronglyMeasurable ?_ hi ?_
  · exact Eventually.of_forall fun ω y hy => by
      have h := hbound y hy ω
      linarith [norm_nonneg (f (y + Z ω))]
  · exact Eventually.of_forall fun ω y hy => by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (hf.differentiable_one (y + Z ω)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (Z ω))

include hZ hMom in
omit [NormedSpace ℝ E] in
/-- Averaged continuous polynomial functions are continuous, even for operator-valued targets. -/
theorem continuous_integral_translate {f : E → Y} (hf : Continuous f)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ d) :
    Continuous (fun y => ∫ ω, f (y + Z ω) ∂μ) := by
  obtain ⟨C, hC, d, hb⟩ := hg
  apply continuous_iff_continuousAt.mpr
  intro x
  let bound : Ω → ℝ := fun ω => C * (2 + ‖x‖) ^ d * (1 + ‖Z ω‖) ^ d
  apply continuousAt_of_dominated (bound := bound)
    (Eventually.of_forall fun y => (hf.comp_stronglyMeasurable (stronglyMeasurable_const.add hZ)).aestronglyMeasurable)
    ?_ ((hMom d).const_mul (C * (2 + ‖x‖) ^ d))
    (Eventually.of_forall fun ω => (hf.comp (continuous_id.add continuous_const)).continuousAt)
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
  exact Eventually.of_forall fun ω => (hb _).trans (by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (translate_polynomial_bound x y (Z ω) hy) d) hC
    simpa only [Pi.add_apply, id_eq, mul_pow, mul_assoc, bound] using hp)

end
end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.IntegralSmooth

/-! # Joint continuity under an auxiliary Gaussian scaling -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- A continuous bounded variance amplitude gives joint operator-norm continuity of averaged
polynomial functions. This includes value, gradient, Hessian, and covariance-trace integrands. -/
theorem continuousOn_integral_scaled_translate
    {E Y Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → E) (hZ : StronglyMeasurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → Y} (hf : Continuous f)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ d)
    (a : ℝ → ℝ) (ha : Continuous a) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |a t| ≤ R) :
    ContinuousOn (fun p : ℝ × E => ∫ ω, f (p.2 + a p.1 • Z ω) ∂μ)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
  obtain ⟨C, hC, d, hb⟩ := hg
  intro p hp
  let B : ℝ := 2 + ‖p.2‖ + R
  let bound : Ω → ℝ := fun ω => C * B ^ d * (1 + ‖Z ω‖) ^ d
  have hi : Integrable bound μ := (hMom d).const_mul (C * B ^ d)
  have hmeas (q : ℝ × E) : StronglyMeasurable (fun ω => f (q.2 + a q.1 • Z ω)) :=
    hf.comp_stronglyMeasurable (stronglyMeasurable_const.add (hZ.const_smul _))
  apply continuousWithinAt_of_dominated
    (Eventually.of_forall fun q => (hmeas q).aestronglyMeasurable)
    (bound := bound) ?_ hi
  · exact Eventually.of_forall fun ω =>
      ((hf.comp (continuous_snd.add ((ha.comp continuous_fst).smul continuous_const))).continuousAt).continuousWithinAt
  · have hlocal : ∀ᶠ q in 𝓝[Icc (0 : ℝ) 1 ×ˢ (univ : Set E)] p, q.2 ∈ Metric.ball p.2 1 :=
      (continuous_snd.tendsto p).eventually (Metric.ball_mem_nhds p.2 (by norm_num)) |>.filter_mono nhdsWithin_le_nhds
    filter_upwards [hlocal, self_mem_nhdsWithin] with q hq hqset
    exact Eventually.of_forall fun ω => by
      have htri := norm_add_le q.2 (a q.1 • Z ω)
      rw [norm_smul, Real.norm_eq_abs] at htri
      have ham := mul_le_mul_of_nonneg_right (hbound q.1 hqset.1) (norm_nonneg (Z ω))
      have hnorm : ‖q.2‖ ≤ ‖q.2 - p.2‖ + ‖p.2‖ := by
        simpa only [sub_add_cancel] using norm_add_le (q.2 - p.2) p.2
      have hdist : ‖q.2 - p.2‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hq
      have harg : 1 + ‖q.2 + a q.1 • Z ω‖ ≤ B * (1 + ‖Z ω‖) := by
        dsimp [B]
        nlinarith [norm_nonneg p.2, norm_nonneg (Z ω),
          mul_nonneg (norm_nonneg p.2) (norm_nonneg (Z ω))]
      exact (hb _).trans (by
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg d) hC
        simpa only [mul_pow, mul_assoc, bound] using hh)

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.NormMoment
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Combining the mean and the upper fluctuation of a Gaussian norm -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The deterministic mean plus upper fluctuation controls the whole nonnegative Lᵖ norm. -/
theorem lpNorm_sq_le_mean_add_positivePart {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ : Integrable Z μ)
    (hf : MemLp (fun ω => max (Z ω - ∫ x, Z x ∂μ) 0) (ENNReal.ofReal p) μ) :
    MemLp Z (ENNReal.ofReal p) μ ∧
    (eLpNorm Z (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      2 * (∫ x, Z x ∂μ) ^ 2 + 2 *
        (eLpNorm (fun ω => max (Z ω - ∫ x, Z x ∂μ) 0) (ENNReal.ofReal p) μ).toReal ^ 2 := by
  let m := ∫ x, Z x ∂μ
  let f : Ω → ℝ := fun ω => max (Z ω - m) 0
  have hm : 0 ≤ m := integral_nonneg hZ0
  have hmf : MemLp (fun ω => m + f ω) (ENNReal.ofReal p) μ := (memLp_const m).add hf
  have hle (ω : Ω) : ‖Z ω‖ ≤ m + f ω := by
    rw [Real.norm_of_nonneg (hZ0 ω)]
    have hh := le_max_left (Z ω - m) 0
    linarith only [hh]
  have hzmem := hmf.mono' hZ.aestronglyMeasurable (ae_of_all _ hle)
  refine ⟨hzmem, ?_⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpn : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have he : lpNorm (fun _ : Ω => m) (ENNReal.ofReal p) μ = m := by
    rw [lpNorm_const' (by positivity) ENNReal.ofReal_ne_top]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, Real.one_rpow, mul_one, Real.norm_of_nonneg hm]
  have htriangle : (eLpNorm Z (ENNReal.ofReal p) μ).toReal ≤
      m + (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
    change lpNorm Z (ENNReal.ofReal p) μ ≤ m + lpNorm f (ENNReal.ofReal p) μ
    apply (lpNorm_mono_real hmf hle).trans
    have hh := lpNorm_add_le (memLp_const m : MemLp (fun _ : Ω => m) (ENNReal.ofReal p) μ)
      (g := f) hpn
    rwa [he] at hh
  have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg htriangle 2
  have halg (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith only [sq_nonneg (a - b)]
  exact hs.trans (halg m _)

/-- Finite covariance images satisfy the exact mean/fluctuation combination used before
inserting the whole-root shell clocks. -/
theorem gaussian_norm_lpNorm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] E) {L p : ℝ}
    (hL : 0 < L) (hp : 1 ≤ p) (hT : ‖T‖ ≤ L) :
    MemLp (fun x : Fin n → ℝ => ‖T (WithLp.toLp 2 x)‖) (ENNReal.ofReal p) (standardGaussianPi n) ∧
    (eLpNorm (fun x : Fin n → ℝ => ‖T (WithLp.toLp 2 x)‖)
      (ENNReal.ofReal p) (standardGaussianPi n)).toReal ^ 2 ≤
      2 * (∫ x : Fin n → ℝ, ‖T (WithLp.toLp 2 x)‖ ∂standardGaussianPi n) ^ 2 + 2 * p * L ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hf := positivePart_centered_norm_lpNorm_sq_le T hL hp0 hT
  have hi := (measure_centered_tail_norm_le T hL (le_refl (0 : ℝ)) hT).1
  have hh := lpNorm_sq_le_mean_add_positivePart (standardGaussianPi n) hp (fun x => norm_nonneg _) hi hf.1
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact add_le_add le_rfl (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hf.2 (by norm_num : (0 : ℝ) ≤ 2))

end ASDExplicitGamma.Gaussian

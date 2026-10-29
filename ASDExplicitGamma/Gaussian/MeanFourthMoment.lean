module

public import ASDExplicitGamma.Gaussian.RioHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # The Gaussian norm's mean from its fourth moment -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Probability L¹-to-L⁴ monotonicity gives the exact mean bound used before concentration. -/
theorem integral_sq_le_sqrt_fourthMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZ : MemLp Z 4 μ) : (∫ ω, Z ω ∂μ) ^ 2 ≤ Real.sqrt (∫ ω, Z ω ^ 4 ∂μ) := by
  have he := eLpNorm_le_eLpNorm_of_exponent_le (f := Z) (μ := μ)
    (show (1 : ℝ≥0∞) ≤ 4 by norm_num)
  have hh := ENNReal.toReal_mono hZ.eLpNorm_ne_top he
  change lpNorm Z 1 μ ≤ (eLpNorm Z 4 μ).toReal at hh
  rw [lpNorm_one_eq_integral_norm hZ.aestronglyMeasurable] at hh
  simp only [Real.norm_of_nonneg (hZ0 _)] at hh
  have hs := pow_le_pow_left₀ (integral_nonneg hZ0) hh 2
  apply hs.trans_eq
  have hr := rio_lpNorm_sq (p := 4) (by norm_num) (by simpa using hZ)
  norm_num only [ENNReal.ofReal_ofNat] at hr
  rw [hr, Real.sqrt_eq_rpow]
  congr 1
  unfold rioMoment
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change |Z ω| ^ (4 : ℝ) = Z ω ^ (4 : ℕ)
    rw [abs_of_nonneg (hZ0 ω), Real.rpow_ofNat]

end ASDExplicitGamma.Gaussian

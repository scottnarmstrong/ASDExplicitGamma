module

public import ASDExplicitGamma.Gaussian.NormalEvenMoments
public import ASDExplicitGamma.Gaussian.RioHolder
public import Mathlib.Algebra.Order.Floor.Ring

/-! # Real-order Gaussian square moments from exact even moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Exact even moments imply the sharp integer-order norm bound. -/
theorem normal_even_lpNorm_sq_le (k : ℕ) (hk : 1 ≤ k) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * (k : ℝ))) (gaussianReal 0 1)).toReal ^ 2 ≤ 2 * (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hp0 : 0 < 2 * (k : ℝ) := mul_pos (by norm_num) hk0
  have hmem := memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal (2 * (k : ℝ))) ENNReal.ofReal_ne_top
  rw [rio_lpNorm_sq hp0 hmem]
  have he : rioMoment (gaussianReal 0 1) (2 * (k : ℝ)) id = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change |x| ^ (2 * (k : ℝ)) = x ^ (2 * k)
      rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
      rw [pow_mul, sq_abs, pow_mul]
  rw [he]
  have hroot : ((2 * (k : ℝ)) ^ k) ^ (2 / (2 * (k : ℝ))) = 2 * (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    have hx : (k : ℝ) * (2 / (2 * (k : ℝ))) = 1 := by field_simp
    rw [hx, Real.rpow_one]
  exact (Real.rpow_le_rpow (integral_nonneg fun x => by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) k) (normal_even_moment_le k)
    (by positivity)).trans_eq hroot

/-- AO-CHI-SQUARE's real-order standard-normal bound, including p = 1. -/
theorem normal_real_lpNorm_sq_le {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p)) (gaussianReal 0 1)).toReal ^ 2 ≤ 2 * p + 2 := by
  let k := Nat.ceil p
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpk : p ≤ (k : ℝ) := Nat.le_ceil p
  have hk : 1 ≤ k := by
    have h := hp.trans hpk
    exact_mod_cast h
  have hf := memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal (2 * (k : ℝ))) ENNReal.ofReal_ne_top
  have he := eLpNorm_le_eLpNorm_of_exponent_le (f := (id : ℝ → ℝ)) (μ := gaussianReal 0 1)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpk (by norm_num : (0 : ℝ) ≤ 2)))
  have hh := ENNReal.toReal_mono hf.eLpNorm_ne_top he
  have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hh 2
  have hklt : (k : ℝ) < p + 1 := Nat.ceil_lt_add_one hp0
  exact (hs.trans (normal_even_lpNorm_sq_le k hk)).trans (by linarith only [hklt])

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.WaveGateNumerics
public import ASDExplicitGamma.Numerics.Scalar.Basic

/-! Uniform-in-label power margins used by the exact planar wave gate. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The residual power pays the exact six-fifths tail margin. -/
theorem wave_power_one_fifth : (6/5:ℝ) ≤ (3:ℝ)^(1/5:ℝ) := by
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ) ≤ 6/5)
    (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) < 5)).mpr
  norm_num [show (5:ℝ) = (5:ℕ) by norm_num, Real.rpow_natCast]

/-- Every positive label retains the source mean power at least three. -/
theorem wave_mean_power_margin (γ : ℝ) (hγ : γ ≤ 1/64) (Λ : ℤ) (hΛ : 1 ≤ Λ) :
    3 ≤ (3:ℝ)^(((7/4:ℝ)-2*γ)*(Λ:ℝ)) := by
  have hx : 1 ≤ ((7/4:ℝ)-2*γ)*(Λ:ℝ) := by
    have hL : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ
    have hc : 1 ≤ (7/4:ℝ)-2*γ := by linarith only [hγ]
    nlinarith only [hc,hL]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hx

/-- Dividing the raw exponent by its rate-1200 power leaves at least six fifths. -/
theorem wave_tail_power_margin (γ : ℝ) (hγ : γ ≤ 1/64) (Λ : ℤ) (hΛ : 1 ≤ Λ) :
    (6/5:ℝ) ≤ (3:ℝ)^(((1/4:ℝ)-2*γ)*(Λ:ℝ)) := by
  apply wave_power_one_fifth.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  have hL : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ
  have hc : (1/5:ℝ) ≤ (1/4:ℝ)-2*γ := by linarith only [hγ]
  exact hc.trans ((le_mul_iff_one_le_right (by linarith only [hc] : (0:ℝ) < 1/4-2*γ)).mpr hL)

/-- The first positive label supplies the factor five used for the union cost. -/
theorem wave_rate_power_ge_five (Λ : ℤ) (hΛ : 1 ≤ Λ) :
    5 ≤ (3:ℝ)^((3/2:ℝ)*(Λ:ℝ)) := by
  have hbase : (5:ℝ) ≤ (3:ℝ)^(3/2:ℝ) := by
    have hh : (5:ℝ) ≤ (27:ℝ)^(2:ℝ)⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ) ≤ 5)
        (by norm_num : (0:ℝ) ≤ 27) (by norm_num : (0:ℝ) < 2)).mpr
        (by norm_num [Real.rpow_natCast])
    have he : (27:ℝ)^(2:ℝ)⁻¹ = (3:ℝ)^(3/2:ℝ) := by
      rw [show (27:ℝ) = (3:ℝ)^3 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    simpa only [he] using hh
  apply hbase.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  have hL : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ
  linarith only [hL]

end ASDExplicitGamma.Gaussian

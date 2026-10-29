module

public import ASDExplicitGamma.Gaussian.WaveGatePowerMargins

/-! Exact physical side/shell ratios and retained real powers in the wave gate. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The buffer factor is geometric, in the old fine side versus the actual
fresh-shell length; it is not a comparison of scalar frames. -/
theorem wave_side_shell_ratio (j Λ : ℤ) :
    ((3:ℝ)^j)/((3:ℝ)^(j+40+Λ)) = (3:ℝ)^(-(40:ℝ)-(Λ:ℝ)) := by
  rw [← zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0), ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- The largest source side ratio is the positive-label-one buffer ratio. -/
theorem wave_label_ratio_le_buffer (Λ : ℤ) (hΛ : 1 ≤ Λ) :
    (3:ℝ)^(-(40:ℝ)-(Λ:ℝ)) ≤ waveBufferRho := by
  unfold waveBufferRho
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  norm_num only [Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
  have hL : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ
  linarith only [hL]

/-- Physical variance growth and two geometric derivatives combine exactly. -/
theorem wave_variance_side_power (γ l : ℝ) :
    (9*γ*(3:ℝ)^(2*γ*l))*((3:ℝ)^(-(40:ℝ)-l))^2 =
      9*γ*(3:ℝ)^(-80+(-2+2*γ)*l) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 2
  push_cast
  ring

/-- The threshold-to-variance power retains the exact 7/4-2gamma exponent. -/
theorem wave_threshold_variance_power (γ l : ℝ) :
    ((3:ℝ)^(-l/8))^2 / (3:ℝ)^(-80+(-2+2*γ)*l) =
      (3:ℝ)^80*(3:ℝ)^(((7/4:ℝ)-2*γ)*l) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    ← Real.rpow_sub (by norm_num : (0:ℝ) < 3)]
  rw [show (3:ℝ)^80 = (3:ℝ)^(80:ℝ) by norm_num [Real.rpow_natCast],
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- Factoring out the desired rate retains the source residual tail power. -/
theorem wave_rate_power_split (γ l : ℝ) :
    (3:ℝ)^(((7/4:ℝ)-2*γ)*l) =
      (3:ℝ)^((3/2:ℝ)*l)*(3:ℝ)^(((1/4:ℝ)-2*γ)*l) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  ring

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.WaveGatePowerIdentities
public import ASDExplicitGamma.Gaussian.WaveGateScalarMargins
public import ASDExplicitGamma.Gaussian.WaveGateMeanPolynomial

/-! Exact threshold comparisons for every positive label. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The squared source threshold, written with the same physical power as the
actual normalized side/variance budget. -/
theorem wave_threshold_sq (γ η l : ℝ) :
    (η*(3:ℝ)^(-l/8))^2 =
      η^2*3^80*(3:ℝ)^(((7/4:ℝ)-2*γ)*l)*(3:ℝ)^(-80+(-2+2*γ)*l) := by
  have hh := (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _))).mp
    (wave_threshold_variance_power γ l)
  rw [mul_pow,hh]
  ring

/-- The actual amplitude/side budget and exact mean gate imply the required
twice-the-mean threshold at every positive label. -/
theorem wave_twice_mean_budget (γ η α : ℝ) (hη : 0 < η) (hα : 0 ≤ α)
    (hγ : γ ≤ 1/64) (Λ : ℤ) (hΛ : 1 ≤ Λ)
    (hbudget : α^2 ≤ 9*γ*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ)))
    (hgate : γ ≤ η^2*3^80/(12*waveBufferMean^2)) :
    α*waveBufferMean ≤ (η*(3:ℝ)^(-(Λ:ℝ)/8))/2 := by
  have hg := wave_mean_gate_square γ η waveBufferMean
    ((3:ℝ)^(((7/4:ℝ)-2*γ)*(Λ:ℝ))) wave_buffer_mean_pos
    (wave_mean_power_margin γ hγ Λ hΛ) hgate
  have hh : 4*(α*waveBufferMean)^2 ≤ (η*(3:ℝ)^(-(Λ:ℝ)/8))^2 := by
    calc
      _ = (4*waveBufferMean^2)*α^2 := by ring
      _ ≤ (4*waveBufferMean^2)*(9*γ*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ))) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (36*γ*waveBufferMean^2)*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ)) := by ring
      _ ≤ (η^2*3^80*(3:ℝ)^(((7/4:ℝ)-2*γ)*(Λ:ℝ)))*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ)) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = _ := (wave_threshold_sq γ η (Λ:ℝ)).symm
  have hx := mul_nonneg hα wave_buffer_mean_pos.le
  have hy : 0 ≤ η*(3:ℝ)^(-(Λ:ℝ)/8) := by positivity
  nlinarith only [hh,hx,hy]

/-- Cancel precisely the retained physical power in the raw Gaussian exponent. -/
theorem wave_raw_exponent_identity (γ η E l : ℝ) (hγ : 0 < γ) (hE : 0 < E) :
    (η*(3:ℝ)^(-l/8))^2/(72*γ*(3:ℝ)^(-80+(-2+2*γ)*l)*E^2) =
      (3:ℝ)^((3/2:ℝ)*l)*(η^2*3^80*(3:ℝ)^(((1/4:ℝ)-2*γ)*l)/(72*γ*E^2)) := by
  rw [wave_threshold_sq γ η l, wave_rate_power_split γ l]
  have hp : (3:ℝ)^(-80+(-2+2*γ)*l) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [hp,hγ.ne',hE.ne']

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.WaveGateThresholdBudget

/-! Sharp rate comparison from the actual physical amplitude/side budget. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The raw Gaussian exponent pays the full source rate plus union allowance
for every positive label, with the buffer power still present. -/
theorem wave_exponent_budget (γ η α E R : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hE : 0 < E) (hR : 0 < R) (hg : γ ≤ 1/64) (Λ : ℤ) (hΛ : 1 ≤ Λ)
    (hbudget : α^2 ≤ 9*γ*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ)))
    (hgate : γ ≤ η^2*3^80/(60*E^2*R)) :
    R*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ)) ≤ (η*(3:ℝ)^(-(Λ:ℝ)/8))^2/(8*(α*E)^2) := by
  have hden : 8*(α*E)^2 ≤ 72*γ*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ))*E^2 := by
    calc
      _ = (8*E^2)*α^2 := by ring
      _ ≤ (8*E^2)*(9*γ*(3:ℝ)^(-80+(-2+2*γ)*(Λ:ℝ))) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by ring
  have hraw := div_le_div_of_nonneg_left (sq_nonneg (η*(3:ℝ)^(-(Λ:ℝ)/8)))
    (by positivity : 0 < 8*(α*E)^2) hden
  apply le_trans ?_ hraw
  rw [wave_raw_exponent_identity γ η E (Λ:ℝ) hγ hE]
  have hh := wave_tail_gate_exponent γ η E R
    ((3:ℝ)^(((1/4:ℝ)-2*γ)*(Λ:ℝ))) hγ hE hR
    (wave_tail_power_margin γ hg Λ hΛ) hgate
  simpa only [mul_comm R] using
    mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _).le

end ASDExplicitGamma.Gaussian

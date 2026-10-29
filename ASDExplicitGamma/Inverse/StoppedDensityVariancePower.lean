module

public import ASDExplicitGamma.Inverse.WeightedLocalizationRadius

/-! The exact retained PE variance power, with the true layer volume intact. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

theorem density_root_weight_power (R : ℕ) :
    (1/9:ℝ)^R = (3:ℝ)^(-(2*(R:ℝ))) := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),
    show 2*(R:ℝ) = ((2*R:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast,pow_mul]
  norm_num [one_div_pow,one_div]

theorem density_alpha_square (R : ℕ) :
    ((3:ℝ)^(-(R:ℝ)))^2 = (1/9:ℝ)^R := by
  rw [density_root_weight_power,← Real.rpow_natCast ((3:ℝ)^(-(R:ℝ))) 2,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  norm_num
  ring

/-- The variance retains sqrt(v); only the source choice N<=3*3^(R/6)
is used to obtain the exact retained decay rate nu_1=5/6. -/
theorem density_variance_power_bound (p β v : ℝ) (hp : 0 ≤ p) (hβ : 0 ≤ β) (R : ℕ) :
    4*Real.sqrt (p*21^2*β*(3:ℝ)^(2*(R/6+1))*(1/9:ℝ)^R*v) ≤
      4*Real.sqrt (p*63^2*β)*Real.sqrt v*(3:ℝ)^(-(5/6:ℝ)*(R:ℝ)) := by
  let N : ℝ := (3:ℝ)^(R/6+1)
  let α : ℝ := (3:ℝ)^(-(R:ℝ))
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hN2 : (3:ℝ)^(2*(R/6+1)) = N^2 := by
    dsimp only [N]
    rw [← pow_mul,Nat.mul_comm (R/6+1) 2]
  have hNs : N ≤ 3*(3:ℝ)^((R:ℝ)/6) := by
    simpa only [N,localizationCutoffRadius,Nat.cast_pow,Nat.cast_ofNat] using! localization_cutoff_radius_le R
  have ha : α^2 = (1/9:ℝ)^R := density_alpha_square R
  have hQ : 0 ≤ N/3*α := by positivity
  have hK : 0 ≤ p*63^2*β := by positivity
  have hvar : p*21^2*β*N^2*(1/9:ℝ)^R*v = (p*63^2*β)*(N/3*α)^2*v := by
    rw [← ha]
    ring
  have hsq : Real.sqrt (p*21^2*β*N^2*(1/9:ℝ)^R*v) =
      Real.sqrt (p*63^2*β)*(N/3*α)*Real.sqrt v := by
    rw [hvar,Real.sqrt_mul (mul_nonneg hK (sq_nonneg _)),Real.sqrt_mul hK,
      Real.sqrt_sq_eq_abs,abs_of_nonneg hQ]
  have hdecay : N/3*α ≤ (3:ℝ)^(-(5/6:ℝ)*(R:ℝ)) := by
    calc
      _ ≤ (3:ℝ)^((R:ℝ)/6)*α := mul_le_mul_of_nonneg_right (by linarith only [hNs]) hα
      _ = _ := by
        dsimp only [α]
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        congr 1
        ring
  rw [hN2,hsq]
  have hh := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ 4*Real.sqrt (p*63^2*β)*Real.sqrt v by positivity)
  convert hh using 1
  ring

end
end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.StoppedDensityVariancePower

/-! The exact retained PE linear Bernstein power. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The linear Bernstein term retains nu_2=(10-m)/6 with its full source
coefficient 4p*63^2*12^m; no layer-weight envelope enters. -/
theorem density_linear_power_bound (p : ℝ) (hp : 0 ≤ p) (m R : ℕ) :
    4*p*21^2*4^m*(3:ℝ)^((R/6+1)*(m+2))*(1/9:ℝ)^R ≤
      4*p*63^2*12^m*(3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ)) := by
  let N : ℝ := (3:ℝ)^(R/6+1)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hNs : N ≤ 3*(3:ℝ)^((R:ℝ)/6) := by
    simpa only [N,localizationCutoffRadius,Nat.cast_pow,Nat.cast_ofNat] using! localization_cutoff_radius_le R
  have hpower := pow_le_pow_left₀ hN hNs (m+2)
  have h12 : (4:ℝ)^m*(3:ℝ)^m = (12:ℝ)^m := by rw [← mul_pow]; norm_num
  have hconst : 4*p*21^2*4^m*(3:ℝ)^(m+2) = 4*p*63^2*12^m := by
    rw [pow_add (3:ℝ) m 2,← h12]
    ring
  have hdecay : ((3:ℝ)^((R:ℝ)/6))^(m+2)*(1/9:ℝ)^R =
      (3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ)) := by
    rw [density_root_weight_power,← Real.rpow_natCast ((3:ℝ)^((R:ℝ)/6)) (m+2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [pow_mul (3:ℝ) (R/6+1) (m+2)]
  calc
    _ ≤ 4*p*21^2*4^m*(3*(3:ℝ)^((R:ℝ)/6))^(m+2)*(1/9:ℝ)^R := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = (4*p*21^2*4^m*(3:ℝ)^(m+2))*(((3:ℝ)^((R:ℝ)/6))^(m+2)*(1/9:ℝ)^R) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hconst,hdecay]

end
end ASDExplicitGamma.Inverse

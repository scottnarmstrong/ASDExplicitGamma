module

public import ASDExplicitGamma.Native.OldSignedMeanSlopeMajorant
public import ASDExplicitGamma.Inverse.BankDepthArithmetic

/-! Rational geometric ratios for inverse-weighted OLD source mean transport. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Scalar Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- Exact square certificates for the weak-history discount. -/
theorem old_signed_weak_discount_caps :
    (577/1000:ℝ)≤ inverseHistoryDiscount^2 ∧ inverseHistoryDiscount^2≤289/500 := by
  have hsq : (inverseHistoryDiscount^2)^2=(1/3:ℝ) := by
    rw [←pow_mul]
    unfold inverseHistoryDiscount
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    norm_num [Real.rpow_neg,Real.rpow_natCast]
  constructor
  · apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤577/1000) (sq_nonneg inverseHistoryDiscount)).mp
    rw [hsq]
    norm_num
  · apply (sq_le_sq₀ (sq_nonneg inverseHistoryDiscount) (by norm_num : (0:ℝ)≤289/500)).mp
    rw [hsq]
    norm_num

/-- The inverse depth clock and weak-history discount form a fixed
geometric factor, uniformly for every permitted model gamma. -/
theorem old_signed_weighted_mean_depth_weight (M : ABKModel 2)
    (hg : M.gamma≤gammaZero) (j : ℕ) :
    inverseHistoryDiscount^(2*j)*bankDepthFrame M j ≤ ((289/500:ℝ)*(1001/1000))^j := by
  have hc : (3:ℝ)^(2*M.gamma)≤1001/1000 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2))).trans old_signed_full64_clock_caps.1
  have hh := mul_le_mul old_signed_weak_discount_caps.2 hc
    (by positivity : (0:ℝ)≤(3:ℝ)^(2*M.gamma)) (by norm_num : (0:ℝ)≤289/500)
  have hp := pow_le_pow_left₀ (mul_nonneg (sq_nonneg inverseHistoryDiscount) (by positivity)) hh j
  rw [mul_pow,←pow_mul,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)] at hp
  exact hp

/-- Normalization and the two complete geometric sums pass the literal
0.018 slope gate. This is a rational certificate, not a floating estimate. -/
theorem old_signed_weighted_mean_slope_numeric :
    (423/1000:ℝ)*(3683/2500)*(383/250000)*
      (3*(251/250)/(1-29/50)+(3/625)*(509/500)*
        (2050/(1-13/200)+6*(13/200)/(1-13/200)^2)) ≤ 9/500 := by
  norm_num

end
end ASDExplicitGamma.Native

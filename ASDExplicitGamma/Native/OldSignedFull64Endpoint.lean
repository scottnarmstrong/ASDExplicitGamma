module

public import ASDExplicitGamma.Native.OldSignedFull64Control
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import ASDExplicitGamma.Cold.NativeStrongHistory

/-! Rational endpoint gates for the retained full64 OLD history slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Scalar Inverse Cold Numerics.Inverse
noncomputable section

/-- Exact polynomial certification of the two history discounts. -/
theorem old_signed_history_discount_caps :
    1-inverseHistoryDiscount≤241/1000 ∧ coldHistoryBeta≤849/1000 := by
  have ha : inverseHistoryDiscount^4=(1/3:ℝ) := by
    unfold inverseHistoryDiscount
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    norm_num [Real.rpow_neg_one]
  have hal : (759/1000:ℝ)≤ inverseHistoryDiscount := by
    apply (pow_le_pow_iff_left₀ (by norm_num) inverse_history_discount_range.1.le
      (by norm_num : (4:ℕ)≠0)).mp
    rw [ha]
    norm_num
  have hb : coldHistoryBeta^20=(1/27:ℝ) := by
    rw [cold_native_beta_power]
    norm_num [Real.rpow_neg,Real.rpow_natCast]
  have hbu : coldHistoryBeta≤849/1000 := by
    apply (pow_le_pow_iff_left₀ coldHistoryBeta_pos.le (by norm_num)
      (by norm_num : (20:ℕ)≠0)).mp
    rw [hb]
    norm_num
  exact ⟨by linarith only [hal],hbu⟩

/-- Each small positive physical clock is certified by the rational
exponential majorant, rather than a floating-point evaluation. -/
theorem old_signed_full64_clock_caps :
    (3:ℝ)^(2*gammaZero)≤1001/1000 ∧
    (3:ℝ)^(8*gammaZero)≤251/250 ∧
    (3:ℝ)^(10*gammaZero)≤251/250 ∧
    (3:ℝ)^(46*gammaZero)≤509/500 := by
  have h2 := inv_three_power_bound (2*gammaZero) (by norm_num [gammaZero]) (by norm_num [gammaZero])
  have h8 := inv_three_power_bound (8*gammaZero) (by norm_num [gammaZero]) (by norm_num [gammaZero])
  have h10 := inv_three_power_bound (10*gammaZero) (by norm_num [gammaZero]) (by norm_num [gammaZero])
  have h46 := inv_three_power_bound (46*gammaZero) (by norm_num [gammaZero]) (by norm_num [gammaZero])
  exact ⟨h2.trans (by norm_num [gammaZero]),h8.trans (by norm_num [gammaZero]),
    h10.trans (by norm_num [gammaZero]),h46.trans (by norm_num [gammaZero])⟩

/-- The slower inverse-trace ratio and the nonlinear response ratio are
strictly inside the rational geometric gates used for the full sum. -/
theorem old_signed_full64_slope_ratios :
    coldHistoryBeta*(3:ℝ)^(2*gammaZero)≤17/20 ∧
    coldHistoryBeta*(3:ℝ)^(8*gammaZero)/9≤1/10 := by
  have hc := old_signed_full64_clock_caps
  have hb := old_signed_history_discount_caps.2
  constructor
  · exact (mul_le_mul hb hc.1 (by positivity) (by norm_num)).trans (by norm_num)
  · have hh := mul_le_mul hb hc.2.1 (by positivity) (by norm_num)
    exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤9)).trans (by norm_num)

/-- All constants in the complete auxiliary slope sum are checked exactly. -/
theorem old_signed_full64_slope_numeric :
    (241/1000:ℝ)*(383/250000)*
      (120*(251/250)/(1-17/20)+(28/125)*(509/500)*
        (2050/(1-1/10)+6*(1/10)/(1-1/10)^2))≤49/100 := by
  norm_num

end
end ASDExplicitGamma.Native

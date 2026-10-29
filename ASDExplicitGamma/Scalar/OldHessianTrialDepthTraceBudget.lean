module

public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment

/-! Complete raw-profile budgets for the grouped OLD weak payments. The
actual global and local bank reserves are kept as distinct coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Inverse Cold Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The baseline frame times the full raw L2 trace envelope has the same
quadratic-geometric 1900 payment, without its depth population multiplier. -/
theorem old_hessian_depth_trace_series_bound (M : ABKModel 2) (hg : M.gamma≤gammaZero) :
    (∑' j : ℕ,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))) ≤
        theta M*(invTraceM:ℝ)*1900 := by
  let C := fun j : ℕ => theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  have hθ : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0≤(invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC (j : ℕ) : 0≤C j := by dsimp [C]; positivity
  have hp (j : ℕ) : inverseHistoryDiscount^(2*j)*bankDepthFrame M j*C j ≤
      ((10^46:ℝ)/3)*(inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*C j) := by
    have hpop : (1:ℝ)≤(9:ℝ)^((j:ℝ)/128) := Real.one_le_rpow (by norm_num) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hpop
      (mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le (2*j)) (bankDepthFrame_pos M j).le) (hC j))
    simp only [mul_one] at hh
    apply hh.trans_eq
    unfold inverseBankDepthReserve inverseBankReserve
    norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
    ring
  have hs := old_signed_depth_trace_budget_summable M hg
  have hr := (old_signed_depth_rare_summable M hg).mul_left ((10^46:ℝ)/3)
  have hh := hs.tsum_le_tsum hp hr
  rw [tsum_mul_left] at hh
  have hb := mul_le_mul_of_nonneg_left (old_signed_directional_rare_series_bound M hg)
    (by norm_num : (0:ℝ)≤(10^46:ℝ)/3)
  exact hh.trans (hb.trans_eq (by norm_num [inverseBankReserve]; ring))

/-- The global beta tail through order three is bounded by the same
coefficient thirteen already proved for the larger OLD local baseline. -/
theorem old_hessian_global_rare_tail_thirteen (ε C : ℝ) (k : ℕ) (hk : k≤3)
    (hε : 0≤ε) (hεsmall : ε≤1/1000) (hC : 0≤C) :
    rareExpansionTail (14103/10000:ℝ) ε C k ≤ 13*ε*C := by
  have hm : rareExpansionTail (14103/10000:ℝ) ε C k≤rareExpansionTail (3683/2500:ℝ) ε C k := by
    unfold rareExpansionTail
    apply Finset.sum_le_sum
    intro i _
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14103/10000)
      (by norm_num : (14103/10000:ℝ)≤3683/2500) (k-i)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) (pow_nonneg hε i)) hC
  exact hm.trans (old_signed_rare_power_thirteen ε C hε hεsmall hC k (by omega))

end
end ASDExplicitGamma.Scalar

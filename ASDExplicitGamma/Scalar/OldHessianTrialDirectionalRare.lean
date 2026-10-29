module

public import ASDExplicitGamma.Scalar.OldHessianTrialWeakRareBudget

/-! The unweighted directional proxy keeps half of the scaled Xi reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Inverse
noncomputable section

/-- With zero global bank power, the global rare tail vanishes. The full
local grouped rare series fits inside half of the theta-scaled reserve. -/
theorem old_hessian_weak_rare_zero_half_reserve (M : ABKModel 2) (hg : M.gamma≤gammaZero) :
    (∑' j,oldHessianWeakRareBudget M 0 j)≤(1/(2*10^12):ℝ)*theta M := by
  let p := 1-inverseHistoryDiscount^2
  let F := fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
    rawWeakTraceProfileEnvelope M j
  have hp : 0≤p := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have he : oldHessianWeakRareBudget M 0=(fun j => (p*5)*F j) := by
    funext j
    norm_num [oldHessianWeakRareBudget,rareExpansionTail,p,F]
    ring
  rw [he,tsum_mul_left]
  have hbound := mul_le_mul_of_nonneg_left (old_signed_directional_rare_series_bound M hg)
    (mul_nonneg hp (by norm_num : (0:ℝ)≤5))
  have hM0 : 0≤(invTraceM:ℝ) := by rw [invTrace_coefficient.1]; positivity
  have hM : (invTraceM:ℝ)≤10^6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hcoef : p*5*(3/10^46:ℝ)*(invTraceM:ℝ)*1900≤(1/(2*10^12):ℝ) := by
    have hp1 : p≤1 := sub_le_self _ (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_right hp1 (by norm_num : (0:ℝ)≤5*(3/10^46:ℝ)))
        hM hM0 (by norm_num : (0:ℝ)≤1*(5*(3/10^46:ℝ)))) (by norm_num : (0:ℝ)≤1900)
    have heq : p*5*(3/10^46:ℝ)*(invTraceM:ℝ)*1900=(p*(5*(3/10^46:ℝ))*(invTraceM:ℝ))*1900 := by ring
    rw [heq]
    exact hh.trans (by norm_num)
  have hlast := mul_le_mul_of_nonneg_right hcoef (cold_theta_pos M).le
  apply hbound.trans
  convert hlast using 1
  norm_num only [inverseBankReserve,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

end
end ASDExplicitGamma.Scalar

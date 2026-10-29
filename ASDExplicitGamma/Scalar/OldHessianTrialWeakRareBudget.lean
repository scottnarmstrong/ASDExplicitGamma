module

public import ASDExplicitGamma.Scalar.OldHessianTrialDepthTraceBudget
public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget
public import ASDExplicitGamma.Native.OldSignedRareTailProduct

/-! All global/local rare terms of the scalar grouped weak proxy fit the
same theta-scaled reserve, including their infinite depth tail. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Inverse Cold Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The actual raw trace profile is nonnegative at every weak depth. -/
theorem old_hessian_raw_profile_nonneg (M : ABKModel 2) (j : ℕ) :
    0≤rawWeakTraceProfileEnvelope M j := by
  have hθ : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0≤(invTraceM:ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

/-- The deterministic budget for both correlated rare payments at depthj. -/
def oldHessianWeakRareBudget (M : ABKModel 2) (k j : ℕ) : ℝ :=
  (1-inverseHistoryDiscount^2)*inverseHistoryDiscount^(2*j)*
    ((3683/2500:ℝ)*bankDepthFrame M j*
      rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) (rawWeakTraceProfileEnvelope M j) k+
    (14103/10000:ℝ)^k*(5*inverseBankDepthReserve .localInverse M j)*rawWeakTraceProfileEnvelope M j)

/-- A rational comparison for the two distinct scalar-grouped reserves. -/
theorem old_hessian_grouped_rare_coefficient (x p z : ℝ)
    (hx0 : 0≤x) (hx3 : x≤3) (hp1 : p≤1) (hz0 : 0≤z) (hzM : z≤10^6) :
    p*((3683/2500:ℝ)*13*(5/10^24:ℝ)+5*x*(3/10^46:ℝ))*z*1900≤(1/10^12:ℝ) := by
  have hc0 : 0≤(3683/2500:ℝ)*13*(5/10^24:ℝ)+5*x*(3/10^46:ℝ) := by positivity
  have hc : (3683/2500:ℝ)*13*(5/10^24:ℝ)+5*x*(3/10^46:ℝ)≤1/10^22 := by
    calc
      _ ≤ (3683/2500:ℝ)*13*(5/10^24:ℝ)+5*3*(3/10^46:ℝ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx3 (by norm_num)) (by norm_num))
      _ ≤ _ := by norm_num
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul hp1 hc hc0 (by norm_num)) hzM hz0
      (by norm_num : (0:ℝ)≤1*(1/10^22:ℝ))) (by norm_num : (0:ℝ)≤1900)
  exact hh.trans (by norm_num)

/-- Every rare-depth budget is nonnegative. -/
theorem old_hessian_weak_rare_budget_nonneg (M : ABKModel 2) (k j : ℕ) :
    0≤oldHessianWeakRareBudget M k j := by
  have hpref : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hC := old_hessian_raw_profile_nonneg M j
  have ht := old_signed_rare_tail_nonneg (14103/10000:ℝ) (5/10^24:ℝ)
    (rawWeakTraceProfileEnvelope M j) (by norm_num) (by norm_num) hC k
  have hreserve : 0 ≤ inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve
    have hb := (bankDepthFrame_pos M j).le
    have hr : 0≤(inverseBankReserve .localInverse:ℝ) := by norm_num [inverseBankReserve]
    positivity
  unfold oldHessianWeakRareBudget
  have hb := (bankDepthFrame_pos M j).le
  have ha := inverse_history_discount_range.1.le
  positivity

/-- The full infinite grouped rare budget lies inside the exact scaled
reserve. No truncation or independence enters this comparison. -/
theorem old_hessian_weak_rare_budget (M : ABKModel 2) (hg : M.gamma≤gammaZero)
    (k : ℕ) (hk : k≤3) :
    Summable (oldHessianWeakRareBudget M k) ∧
      (∑' j,oldHessianWeakRareBudget M k j)≤(1/10^12:ℝ)*theta M := by
  let C := rawWeakTraceProfileEnvelope M
  let A := (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*13*(5/10^24:ℝ)
  let D := (1-inverseHistoryDiscount^2)*(14103/10000:ℝ)^k*5
  let F := fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*C j
  let G := fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*C j
  have hpref : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hA : 0≤A := by dsimp [A]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hF : Summable F := old_signed_depth_trace_budget_summable M hg
  have hG : Summable G := old_signed_depth_rare_summable M hg
  have hmajor (j : ℕ) : oldHessianWeakRareBudget M k j≤A*F j+D*G j := by
    have ht := old_hessian_global_rare_tail_thirteen (5/10^24:ℝ) (C j) k hk
      (by norm_num) (by norm_num) (old_hessian_raw_profile_nonneg M j)
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num : (0:ℝ)≤3683/2500)
        (bankDepthFrame_pos M j).le))
      (le_refl ((14103/10000:ℝ)^k*(5*inverseBankDepthReserve .localInverse M j)*C j))
    have hw := mul_le_mul_of_nonneg_left hh
      (mul_nonneg hpref (pow_nonneg inverse_history_discount_range.1.le (2*j)))
    exact hw.trans_eq (by dsimp [A,D,F,G]; ring)
  have hs := ((hF.mul_left A).add (hG.mul_left D)).of_nonneg_of_le
    (old_hessian_weak_rare_budget_nonneg M k) hmajor
  refine ⟨hs,?_⟩
  have hh := hs.tsum_le_tsum hmajor ((hF.mul_left A).add (hG.mul_left D))
  rw [Summable.tsum_add (hF.mul_left A) (hG.mul_left D),tsum_mul_left,tsum_mul_left] at hh
  have hbound := add_le_add
    (mul_le_mul_of_nonneg_left (old_hessian_depth_trace_series_bound M hg) hA)
    (mul_le_mul_of_nonneg_left (old_signed_directional_rare_series_bound M hg) hD)
  have hβ : (14103/10000:ℝ)^k≤3 :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤14103/10000) hk).trans (by norm_num)
  have hM : (invTraceM:ℝ)≤10^6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hM0 : 0≤(invTraceM:ℝ) := by rw [invTrace_coefficient.1]; positivity
  have hnum := old_hessian_grouped_rare_coefficient ((14103/10000:ℝ)^k)
    (1-inverseHistoryDiscount^2) (invTraceM:ℝ) (pow_nonneg (by norm_num) k) hβ
    (sub_le_self _ (sq_nonneg _)) hM0 hM
  have hθ : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hlast := mul_le_mul_of_nonneg_right hnum hθ
  apply (hh.trans hbound).trans
  convert hlast using 1
  norm_num only [A,D,inverseBankReserve,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

end
end ASDExplicitGamma.Scalar

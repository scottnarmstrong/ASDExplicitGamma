module

public import ASDExplicitGamma.Native.OldSignedDepthSeriesArithmetic
public import ASDExplicitGamma.Native.GenericSourceShortTail

/-! Explicit complete rare-depth payment, inside the source delta reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Scalar Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The full correlated depth reserve is bounded by the exact quadratic
geometric sum, including the depth-population factor. -/
theorem old_signed_directional_rare_series_bound (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    (∑' j : ℕ,inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
      (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))) ≤
      (inverseBankReserve .localInverse:ℝ)*theta M*(invTraceM:ℝ)*1900 := by
  let c := (inverseBankReserve .localInverse:ℝ)*theta M*(invTraceM:ℝ)
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (by norm_num [inverseBankReserve]) htheta) hM0
  have hgeom := native_source_quadratic_geometric_sum (9/10) (by norm_num) (by norm_num)
  have hh := (old_signed_depth_rare_summable M hg).tsum_le_tsum
    (g := fun j : ℕ => c*(((j:ℝ)+1)^2*(9/10:ℝ)^j)) (fun j => ?_) (hgeom.1.mul_left c)
  · rw [tsum_mul_left,hgeom.2] at hh
    norm_num only [show (1+(9/10:ℝ))/(1-9/10)^3=1900 by norm_num] at hh
    exact hh
  · let q := (3:ℝ)^(-(1/2:ℝ)+2*M.gamma+6*gammaZero+1/64)
    have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
    have he : inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
        (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))=
        c*(((j:ℝ)+1)^2*q^j) := by
      unfold inverseBankDepthReserve
      calc
        _ = c*(((j:ℝ)+1)^2*(inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
            (9:ℝ)^((j:ℝ)/128)*(3:ℝ)^(6*gammaZero*j))) := by dsimp [c]; ring
        _ = _ := by rw [old_signed_depth_rare_weight]
    rw [he]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hq0 (old_signed_depth_rare_ratio M hg) j) (sq_nonneg _)) hc

/-- Even thirteen such correlated payments fit inside the allocated delta.
The actual theta factor is preserved; there is no unscaled raw diagnostic. -/
theorem old_signed_directional_rare_delta (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    13*(1-inverseHistoryDiscount^2)*
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
        (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))) ≤ (1/10^12:ℝ)*theta M := by
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hc1 : 1-inverseHistoryDiscount^2 ≤ 1 := sub_le_self _ (sq_nonneg _)
  have hM : (invTraceM:ℝ) ≤ 10^6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hh := mul_le_mul_of_nonneg_left (old_signed_directional_rare_series_bound M hg)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 13) hc)
  have hnum : 13*(1-inverseHistoryDiscount^2)*(inverseBankReserve .localInverse:ℝ)*(invTraceM:ℝ)*1900 ≤
      (1/10^12:ℝ) := by
    rw [show (inverseBankReserve .localInverse:ℝ)=(3/10^46:ℝ) by norm_num [inverseBankReserve]]
    calc
      _ ≤ 13*(1-inverseHistoryDiscount^2)*(3/10^46)*10^6*1900 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM
          (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤13) hc)
            (by norm_num : (0:ℝ)≤3/10^46))) (by norm_num)
      _ = (1-inverseHistoryDiscount^2)*(13*(3/10^46)*10^6*1900) := by ring
      _ ≤ 1*(13*(3/10^46)*10^6*1900) :=
        mul_le_mul_of_nonneg_right hc1 (by norm_num)
      _ ≤ _ := by norm_num
  calc
    _ ≤ 13*(1-inverseHistoryDiscount^2)*((inverseBankReserve .localInverse:ℝ)*theta M*(invTraceM:ℝ)*1900) := hh
    _ = (13*(1-inverseHistoryDiscount^2)*(inverseBankReserve .localInverse:ℝ)*(invTraceM:ℝ)*1900)*theta M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hnum htheta

end
end ASDExplicitGamma.Native

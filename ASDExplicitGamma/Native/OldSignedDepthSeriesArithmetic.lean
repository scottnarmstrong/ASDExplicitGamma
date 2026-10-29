module

public import ASDExplicitGamma.Native.OldSignedDepthDirectionalPayment
public import ASDExplicitGamma.Scalar.InverseHistoryFormula
public import ASDExplicitGamma.Native.GenericSourceTail

/-! Summable complete depth budgets for the inverse-directional payments. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Scalar Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The combined rare-depth ratio stays below the fixed polynomial-geometric
majorant, uniformly throughout the source gamma range. -/
theorem old_signed_depth_rare_ratio (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    (3:ℝ)^(-(1/2:ℝ)+2*M.gamma+6*gammaZero+1/64) ≤ 9/10 := by
  have hpow : (3:ℝ)^(-(1/2:ℝ)+2*M.gamma+6*gammaZero+1/64) ≤ inverseHistoryDiscount := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    dsimp [gammaZero] at hg ⊢
    linarith only [hg]
  have ha : inverseHistoryDiscount < (invAlphaUpper:ℝ) := by
    rw [inverse_history_discount_eq]
    have he : ((3:ℝ)^(1/4:ℝ))⁻¹=(1/3:ℝ)^(1/4:ℝ) := by
      simpa only [one_div] using (Real.inv_rpow (by norm_num : (0:ℝ)≤3) (1/4:ℝ)).symm
    rw [he]
    exact inv_alpha_real.2
  exact hpow.trans (ha.le.trans (by norm_num [invAlphaUpper]))

/-- Exact combination of the squared weak weight, physical frame growth,
raw-trace growth and the depth-population reserve. -/
theorem old_signed_depth_rare_weight (M : ABKModel 2) (j : ℕ) :
    inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (9:ℝ)^((j:ℝ)/128)*(3:ℝ)^(6*gammaZero*j)=
    ((3:ℝ)^(-(1/2:ℝ)+2*M.gamma+6*gammaZero+1/64))^j := by
  rw [inverse_history_discount_power]
  have hn : (9:ℝ)^((j:ℝ)/128)=(3:ℝ)^((j:ℝ)/64) := by
    rw [show (9:ℝ)=(3:ℝ)^2 by norm_num,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
    ring
  rw [hn,bankDepthFrame,←Real.rpow_add (by norm_num : (0:ℝ)<3),
    ←Real.rpow_add (by norm_num : (0:ℝ)<3),←Real.rpow_add (by norm_num : (0:ℝ)<3),
    ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 1
  push_cast
  ring

/-- The complete rare series is summable, before any real tsum is consumed. -/
theorem old_signed_depth_rare_summable (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      inverseBankDepthReserve .localInverse M j*
      (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))) := by
  let c := (inverseBankReserve .localInverse:ℝ)*theta M*(invTraceM:ℝ)
  let q := (3:ℝ)^(-(1/2:ℝ)+2*M.gamma+6*gammaZero+1/64)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hs : Summable (fun j : ℕ => ((j:ℝ)+1)^2*q^j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (pow_nonneg hq0 j))
      (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0
        (old_signed_depth_rare_ratio M hg) j) (sq_nonneg _)) native_source_geom_quadratic_summable
  apply (hs.mul_left c).congr
  intro j
  have hw := old_signed_depth_rare_weight M j
  dsimp only [c,q]
  unfold inverseBankDepthReserve
  calc
    _ = (inverseBankReserve .localInverse:ℝ)*theta M*(invTraceM:ℝ)*((j:ℝ)+1)^2*
        (inverseHistoryDiscount^(2*j)*bankDepthFrame M j*(9:ℝ)^((j:ℝ)/128)*
          (3:ℝ)^(6*gammaZero*j)) := by rw [hw]; ring
    _ = _ := by ring

/-- Removing the population factor still leaves a summable full trace budget. -/
theorem old_signed_depth_trace_budget_summable (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))) := by
  let C := fun j : ℕ => theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  have ht0 : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC0 (j : ℕ) : 0 ≤ C j := by dsimp [C]; positivity
  have hs := (old_signed_depth_rare_summable M hg).mul_left ((10^46:ℝ)/3)
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (bankDepthFrame_pos M j).le) (hC0 j)) _ hs
  intro j
  have hp : (1:ℝ) ≤ (9:ℝ)^((j:ℝ)/128) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le (2*j))
      (bankDepthFrame_pos M j).le) (hC0 j))
  simp only [mul_one] at hh
  apply hh.trans_eq
  unfold inverseBankDepthReserve inverseBankReserve
  dsimp [C]
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedBankPowerRare
public import ASDExplicitGamma.Native.GenericSourceShortTail

/-! Correlated rare payments with the slower quarter-discount weights. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The quarter-discounted raw-trace growth still has a strict geometric margin. -/
theorem old_signed_quarter_trace_ratio :
    (3:ℝ)^(-(1/4:ℝ)+6*gammaZero)≤9/10 := by
  have he : -(1/4:ℝ)+6*gammaZero≤-(1/5:ℝ) := by norm_num [gammaZero]
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) he).trans
  have hx : 0≤(3:ℝ)^(-(1/5:ℝ)) := Real.rpow_nonneg (by norm_num) _
  apply (pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (5:ℕ)≠0)).mp
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  norm_num [Real.rpow_neg_one]

/-- Exact combination of the slower discount and the raw trace clock. -/
theorem old_signed_quarter_trace_weight (j : ℕ) :
    inverseHistoryDiscount^j*(3:ℝ)^(6*gammaZero*j)=
      ((3:ℝ)^(-(1/4:ℝ)+6*gammaZero))^j := by
  rw [inverse_history_discount_eq]
  rw [←Real.rpow_neg_one,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3),←Real.rpow_add (by norm_num : (0:ℝ)<3)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

/-- The complete slow raw-trace reserve is summable and has a rational bound. -/
theorem old_signed_quarter_trace_profile (M : ABKModel 2) :
    let C := fun j : ℕ => theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
    Summable (fun j : ℕ => inverseHistoryDiscount^j*C j) ∧
    (∑' j : ℕ,inverseHistoryDiscount^j*C j)≤theta M*(invTraceM:ℝ)*1900 := by
  intro C
  let c := theta M*(invTraceM:ℝ)
  have hc : 0≤c := mul_nonneg (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])) (by rw [invTrace_coefficient.1]; positivity)
  have hgeom := native_source_quadratic_geometric_sum (9/10) (by norm_num) (by norm_num)
  have hdom := hgeom.1.mul_left c
  have hnonneg (j : ℕ) : 0≤ inverseHistoryDiscount^j*C j := by
    dsimp only [C]
    exact mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (mul_nonneg (mul_nonneg hc (sq_nonneg _)) (Real.rpow_nonneg (by norm_num) _))
  have hbound (j : ℕ) : inverseHistoryDiscount^j*C j≤c*(((j:ℝ)+1)^2*(9/10:ℝ)^j) := by
    calc
      _ = c*(((j:ℝ)+1)^2*(inverseHistoryDiscount^j*(3:ℝ)^(6*gammaZero*j))) := by dsimp only [C,c]; ring
      _ ≤ _ := by
        rw [old_signed_quarter_trace_weight]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) old_signed_quarter_trace_ratio j)
            (sq_nonneg _)) hc
  have hs := Summable.of_nonneg_of_le hnonneg hbound hdom
  refine ⟨hs,?_⟩
  have hh := hs.tsum_le_tsum hbound hdom
  rw [tsum_mul_left,hgeom.2] at hh
  norm_num only [show (1+(9/10:ℝ))/(1-9/10)^3=1900 by norm_num] at hh
  exact hh

end
end ASDExplicitGamma.Native

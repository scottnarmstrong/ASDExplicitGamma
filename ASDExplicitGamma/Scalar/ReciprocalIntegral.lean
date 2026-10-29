module

public import ASDExplicitGamma.Scalar.ReciprocalWeight

/-! Evaluation of the two regions in reciprocal-to-scalar conversion. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory intervalIntegral

/-- The integral over the molecular-to-final reciprocal interval has the common source majorant. -/
theorem reciprocal_integral_bound (nu S Y : ℝ) (hnu : 0<nu) (hS : nu≤S) (hY : 1≤Y) :
    (∫ r in S⁻¹..nu⁻¹,reciprocalWeight S Y r)≤(3*Y-2)*(S^2-nu^2)/2 := by
  have hS0 : 0<S := hnu.trans_le hS
  have hY0 : 0<Y := lt_of_lt_of_le (by norm_num) hY
  have hab : S⁻¹≤nu⁻¹ := (inv_le_inv₀ hS0 hnu).mpr hS
  by_cases hlarge : Y*nu≤S
  · have ham : S⁻¹≤Y/S := by
      rw [← one_div,div_le_div_iff_of_pos_right hS0]
      exact hY
    have hmb : Y/S≤nu⁻¹ := by
      rw [div_le_iff₀ hS0]
      have h : Y≤S/nu := (le_div_iff₀ hnu).mpr hlarge
      simpa only [div_eq_mul_inv,mul_comm] using h
    have hm : 0<Y/S := div_pos hY0 hS0
    have hsplit := integral_add_adjacent_intervals
      (reciprocal_weight_intervalIntegrable S Y S⁻¹ (Y/S) (inv_pos.mpr hS0) hm)
      (reciprocal_weight_intervalIntegrable S Y (Y/S) nu⁻¹ hm (inv_pos.mpr hnu))
    calc
      _ = (∫ r in S⁻¹..Y/S,reciprocalWeight S Y r)+
          ∫ r in Y/S..nu⁻¹,reciprocalWeight S Y r := hsplit.symm
      _ ≤ (Y/S-S⁻¹)*S^3+Y^3*((Y/S)^(-2:ℤ)-(nu⁻¹)^(-2:ℤ))/2 :=
        add_le_add (integral_reciprocal_weight_le_constant S Y _ _ (inv_pos.mpr hS0) ham)
          (integral_reciprocal_weight_le_inverse_cube S Y _ _ hm hmb)
      _ = S^2*(Y-1)+(Y*S^2-Y^3*nu^2)/2 := by
        simp only [zpow_neg,zpow_ofNat]
        field_simp
      _ ≤ _ := reciprocal_large_region_bound nu S Y hY
  · have hsmall : S≤Y*nu := le_of_lt (lt_of_not_ge hlarge)
    exact (integral_reciprocal_weight_le_constant S Y S⁻¹ nu⁻¹ (inv_pos.mpr hS0) hab).trans
      (by simpa only [mul_comm] using reciprocal_small_region_bound nu S Y hnu hS hsmall)

end ASDExplicitGamma.Scalar

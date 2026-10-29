module

public import ASDExplicitGamma.Native.GenericSourceMeans

/-! A proportional rational majorant for the positive child mean exponential.
The constant part and the exp-minus-one part keep their different degrees. -/
@[expose] public section
namespace ASDExplicitGamma.Native

/-- A theta-proportional exponent has an endpoint rational exponential
cap and a theta-proportional exp-minus-one cap, without rounding at theta. -/
theorem native_source_child_exp_majorant (c C theta : ℝ)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hC1 : C<1)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (hcap : c ≤ theta*C) :
    Real.exp c ≤ 1/(1-C) ∧ Real.exp c-1 ≤ theta*(C/(1-C)) := by
  have hcC : c ≤ C := hcap.trans ((mul_le_mul_of_nonneg_right ht1 hC).trans_eq (one_mul _))
  have hc1 : c<1 := hcC.trans_lt hC1
  have hdenC : 0<1-C := sub_pos.mpr hC1
  have hdenc : 0<1-c := sub_pos.mpr hc1
  have hfrac := one_div_le_one_div_of_le hdenC (sub_le_sub_left hcC 1)
  have hexp := Real.exp_bound_div_one_sub_of_interval hc hc1
  have hminus : Real.exp c-1 ≤ c/(1-c) := by
    have he : 1/(1-c)-1=c/(1-c) := by field_simp; ring
    exact (sub_le_sub_right hexp 1).trans_eq he
  refine ⟨hexp.trans hfrac,?_⟩
  apply hminus.trans
  calc
    c/(1-c) = c*(1/(1-c)) := by ring
    _ ≤ (theta*C)*(1/(1-c)) := mul_le_mul_of_nonneg_right hcap (one_div_nonneg.mpr hdenc.le)
    _ ≤ (theta*C)*(1/(1-C)) := mul_le_mul_of_nonneg_left hfrac (mul_nonneg ht0 hC)
    _ = _ := by ring

end ASDExplicitGamma.Native

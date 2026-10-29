module

public import ASDExplicitGamma.Scalar.ReciprocalWeight

/-! A discrete reciprocal drop is dominated by the source weight integral. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Set intervalIntegral

/-- The source reciprocal weight is nonincreasing in its positive reciprocal argument. -/
theorem reciprocal_weight_antitone (S Y : ℝ) (hY : 0≤Y) :
    AntitoneOn (reciprocalWeight S Y) (Ioi 0) := by
  intro a ha b hb hab
  apply min_le_min_left
  simp only [zpow_neg,zpow_ofNat,← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (pow_nonneg hY 3) (pow_pos ha 3)
    (pow_le_pow_left₀ ha.le hab 3)

/-- Both source normalizations bound the viscosity cube by the reciprocal weight. -/
theorem sigma_cube_le_reciprocal_weight (S Y sigma r : ℝ)
    (hsigma : 0<sigma) (hr : 0<r) (hS : sigma≤S) (hY : sigma*r≤Y) :
    sigma^3≤reciprocalWeight S Y r := by
  apply le_min
  · exact pow_le_pow_left₀ hsigma.le hS 3
  · simp only [zpow_neg,zpow_ofNat,← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hr 3)).mpr
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_pos hsigma hr).le hY 3

/-- The genuine one-shell drop is paid by the increasing weight along the reciprocal interval. -/
theorem reciprocal_drop_le_weight_integral (S Y sigma r rnext bill : ℝ)
    (hsigma : 0<sigma) (hrnext : 0<rnext) (hdrop : rnext≤r)
    (hS : sigma≤S) (hY : sigma*r≤Y) (hbill : bill≤(r-rnext)*sigma^3) :
    bill≤∫ t in rnext..r,reciprocalWeight S Y t := by
  have hr : 0<r := hrnext.trans_le hdrop
  have hY0 : 0≤Y := (mul_pos hsigma hr).le.trans hY
  calc
    _ ≤ (r-rnext)*sigma^3 := hbill
    _ ≤ (r-rnext)*reciprocalWeight S Y r := mul_le_mul_of_nonneg_left
      (sigma_cube_le_reciprocal_weight S Y sigma r hsigma hr hS hY) (sub_nonneg.mpr hdrop)
    _ = ∫ t in rnext..r,reciprocalWeight S Y r := by rw [intervalIntegral.integral_const]; rfl
    _ ≤ _ := integral_mono_on hdrop intervalIntegrable_const
      (reciprocal_weight_intervalIntegrable S Y rnext r hrnext hr)
      (fun t ht => reciprocal_weight_antitone S Y hY0 (hrnext.trans_le ht.1) hr ht.2)

end ASDExplicitGamma.Scalar

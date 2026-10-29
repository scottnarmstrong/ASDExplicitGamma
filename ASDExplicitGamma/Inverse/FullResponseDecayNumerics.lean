module

public import ASDExplicitGamma.Inverse.FullResponseResetMomentNumerics
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Real geometric-ratio bounds used in the complete finite-order reset sums. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

theorem full_response_three_neg_99_le :
    (3:ℝ)^(-(99/100:ℝ)) ≤ 34/100 := by
  have hsmall := inv_three_power_bound (1/100:ℝ) (by norm_num)
    (by norm_num : (11/10:ℝ)*(1/100)<1)
  have hsplit : (3:ℝ)^(-(99/100:ℝ)) =
      (1/3:ℝ)*(3:ℝ)^(1/100:ℝ) := by
    rw [show (-(99/100:ℝ))=(-1:ℝ)+(1/100:ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0:ℝ)<3), Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    norm_num
  rw [hsplit]
  calc
    _ ≤ (1/3:ℝ)*(1000/989) := by nlinarith
    _ ≤ 34/100 := by norm_num

theorem full_response_three_neg_49_le :
    (3:ℝ)^(-(49/100:ℝ)) ≤ 59/100 := by
  have hsmall := inv_three_power_bound (1/100:ℝ) (by norm_num)
    (by norm_num : (11/10:ℝ)*(1/100)<1)
  have hhalf : (3:ℝ)^(-(1/2:ℝ)) ≤ 29/50 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3), ← Real.sqrt_eq_rpow]
    rw [← one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3))).2
    have hs : 50/29 ≤ Real.sqrt 3 := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    nlinarith
  have hsplit : (3:ℝ)^(-(49/100:ℝ)) =
      (3:ℝ)^(-(1/2:ℝ))*(3:ℝ)^(1/100:ℝ) := by
    rw [show (-(49/100:ℝ))=(-(1/2:ℝ))+(1/100:ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0:ℝ)<3)]
  rw [hsplit]
  have hsmall' : (3:ℝ)^(1/100:ℝ) ≤ 1000/989 := by
    norm_num at hsmall ⊢
    exact hsmall
  calc
    _ ≤ (29/50:ℝ)*(1000/989) := mul_le_mul hhalf hsmall' (by positivity) (by positivity)
    _ ≤ 59/100 := by norm_num


/-- The first D4 retained decay uses the exact rational .65 envelope. -/
theorem full_response_three_neg_40_le : (3:ℝ)^(-(2/5:ℝ)) ≤ 65/100 := by
  have hh := (inv_root_lower (l := (20/13:ℚ)) (x := 9) (n := 5)
    (by norm_num) (by decide) (by norm_num)).le
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at hh
  have he : (9:ℝ)^(1/5:ℝ)=(3:ℝ)^(2/5:ℝ) := by
    rw [show (9:ℝ)=(3:ℝ)^2 by norm_num,← Real.rpow_natCast (3:ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  rw [he] at hh
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
  have hi := inv_anti₀ (by norm_num : (0:ℝ)<20/13) hh
  norm_num at hi ⊢
  exact hi

end
end ASDExplicitGamma.Inverse

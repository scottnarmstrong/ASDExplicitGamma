module

public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! Positive-power forms of the exact scalar comparisons. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar

/-- NU-SC-H-SOURCE: the strong-history cap before taking fourth powers. -/
theorem source_history_cap :
    (3 : ℝ)^(3/4 : ℝ)*(2379/2500 : ℝ) < 5423/2500 := by
  apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 5423/2500)
  rw [mul_pow]
  have hpow : ((3 : ℝ)^(3/4 : ℝ))^4 = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hpow]
  norm_num

/-- NU-SC-OLD-GROUPED-REMAINDER: the global population factor before taking power 128. -/
theorem global_group_factor : (9 : ℝ)^(89/128 : ℝ) < 5 := by
  apply lt_of_pow_lt_pow_left₀ 128 (by norm_num : (0 : ℝ) ≤ 5)
  have hpow : ((9 : ℝ)^(89/128 : ℝ))^128 = (9 : ℝ)^89 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
    norm_num
  rw [hpow]
  exact_mod_cast global_group_population

/-- Multiply only the global ordinary-bank error by the global population factor. -/
theorem global_group_error :
    (9 : ℝ)^(89/128 : ℝ)*(1/10^24 : ℝ) < 5*(1/10^24 : ℝ) :=
  mul_lt_mul_of_pos_right global_group_factor (by norm_num)

/-- NU-SC-FRAME-RATIOS: both restored-frame comparisons, retaining a positive scale. -/
theorem restored_frame_ratios (R scale : ℝ) (hR : 0 < R) (hs : 0 < scale) :
    (65/22 : ℝ)*R < 3*R ∧
    Real.sqrt (65/22)*scale < Real.sqrt 3*scale ∧ Real.sqrt 3 < 2 := by
  refine ⟨mul_lt_mul_of_pos_right frame_ratio_constants.1 hR,
    mul_lt_mul_of_pos_right ?_ hs, frame_ratio_constants.2⟩
  exact Real.sqrt_lt_sqrt (by norm_num) frame_ratio_constants.1

end ASDExplicitGamma.Numerics.Scalar

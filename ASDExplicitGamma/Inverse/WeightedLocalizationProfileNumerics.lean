module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLayerProfile
public import ASDExplicitGamma.Numerics.Inverse.Layers

/-! Source generating functions consume the literal numeric formulas. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The analytic T is exactly the numeric supplier's rational T after real coercion. -/
theorem localization_profileT_numeric (a z : ℚ) :
    localizationProfileT (a : ℝ) (z : ℝ) = (Numerics.Inverse.invT a z : ℝ) := by
  unfold localizationProfileT Numerics.Inverse.invT
  push_cast
  rfl

/-- The first profile moment is exactly the numeric supplier's Tf. -/
theorem localization_profileTf_numeric (a z : ℚ) :
    localizationProfileTf (a : ℝ) (z : ℝ) = (Numerics.Inverse.invTf a z : ℝ) := by
  unfold localizationProfileTf Numerics.Inverse.invTf
  push_cast
  rfl

/-- Monotonicity of the corrected layer generating function follows from
positive physical weights, despite its subtractive closed formula. -/
theorem localization_layer_profile_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ^ 4 < 27) :
    8 * localizationProfileT (1 / 3) x - 32 * localizationProfileT (1 / 9) x + x ^ 2 ≤
      8 * localizationProfileT (1 / 3) y - 32 * localizationProfileT (1 / 9) y + y ^ 2 := by
  have hxs : x ^ 4 < 27 := (pow_le_pow_left₀ hx hxy 4).trans_lt hy
  exact hasSum_le (fun n => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hx hxy (localizationProfileDepth (n + 1))) (bankLayerWeight_nonneg n))
    (localization_layer_profile_hasSum x hx hxs) (localization_layer_profile_hasSum y (hx.trans hxy) hy)

/-- The weighted first moment has the same source-preserving monotonicity. -/
theorem localization_layer_profile_moment_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ^ 4 < 27) :
    8 * localizationProfileTf (1 / 3) x - 32 * localizationProfileTf (1 / 9) x + 2 * x ^ 2 ≤
      8 * localizationProfileTf (1 / 3) y - 32 * localizationProfileTf (1 / 9) y + 2 * y ^ 2 := by
  have hxs : x ^ 4 < 27 := (pow_le_pow_left₀ hx hxy 4).trans_lt hy
  exact hasSum_le (fun n => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hx hxy (localizationProfileDepth (n + 1)))
      (mul_nonneg (Nat.cast_nonneg _) (bankLayerWeight_nonneg n)))
    (localization_layer_profile_moment_hasSum x hx hxs)
    (localization_layer_profile_moment_hasSum y (hx.trans hxy) hy)

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.WeightedLocalizationProfileMoment

/-! Exact generating functions of the corrected planar layer weights. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The full corrected layer profile, including its central-square correction. -/
theorem localization_layer_profile_hasSum (z : ℝ) (hz : 0 ≤ z) (hsmall : z ^ 4 < 27) :
    HasSum (fun n : ℕ => bankLayerWeight n * z ^ localizationProfileDepth (n + 1))
      (8 * localizationProfileT (1 / 3) z - 32 * localizationProfileT (1 / 9) z + z ^ 2) := by
  have h1 : (1 / 3 : ℝ) ^ 3 * z ^ 4 < 1 := by norm_num; nlinarith only [hsmall]
  have h2 : (1 / 9 : ℝ) ^ 3 * z ^ 4 < 1 := by norm_num; nlinarith only [hsmall]
  have hh := ((localization_profile_hasSum (1 / 3) z (by norm_num) hz h1).mul_left 8).sub
    ((localization_profile_hasSum (1 / 9) z (by norm_num) hz h2).mul_left 32)
  have hs : HasSum (fun n : ℕ => if n = 0 then z ^ 2 else 0) (z ^ 2) := hasSum_ite_eq 0 _
  convert hh.add hs using 1
  funext n
  cases n with
  | zero => norm_num [bankLayerWeight, localizationProfileDepth]; ring
  | succ n => simp only [layerWeight_succ, Nat.succ_ne_zero, ite_false]
              ring

/-- The exact first profile moment of those same physical layer weights. -/
theorem localization_layer_profile_moment_hasSum (z : ℝ) (hz : 0 ≤ z) (hsmall : z ^ 4 < 27) :
    HasSum (fun n : ℕ => (localizationProfileDepth (n + 1) : ℝ) *
      bankLayerWeight n * z ^ localizationProfileDepth (n + 1))
      (8 * localizationProfileTf (1 / 3) z - 32 * localizationProfileTf (1 / 9) z + 2 * z ^ 2) := by
  have h1 : (1 / 3 : ℝ) ^ 3 * z ^ 4 < 1 := by norm_num; nlinarith only [hsmall]
  have h2 : (1 / 9 : ℝ) ^ 3 * z ^ 4 < 1 := by norm_num; nlinarith only [hsmall]
  have hh := ((localization_profile_moment_hasSum (1 / 3) z (by norm_num) hz h1).mul_left 8).sub
    ((localization_profile_moment_hasSum (1 / 9) z (by norm_num) hz h2).mul_left 32)
  have hs : HasSum (fun n : ℕ => if n = 0 then 2 * z ^ 2 else 0) (2 * z ^ 2) := hasSum_ite_eq 0 _
  convert hh.add hs using 1
  funext n
  cases n with
  | zero => norm_num [bankLayerWeight, localizationProfileDepth]; ring
  | succ n => simp only [layerWeight_succ, Nat.succ_ne_zero, ite_false]
              ring

end ASDExplicitGamma.Inverse

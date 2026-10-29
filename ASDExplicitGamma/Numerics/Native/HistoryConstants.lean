module
public import ASDExplicitGamma.Numerics.Native.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Real interpretation of the native history weights and complete returned-cap comparisons. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem native_history_ratio_real : (3 : ℝ)^(-3/20 : ℝ) < (nativeHistoryRatio : ℝ) := by
  have h := ASDExplicitGamma.Numerics.Inverse.inv_root_upper
    (x := (1/27 : ℚ)) (u := nativeHistoryRatio) (n := 20)
    (by decide +kernel) (by decide +kernel) (by decide) native_history_constants.2.2.1
  have he : (3 : ℝ)^(-3/20 : ℝ) = (1/27 : ℝ)^((20 : ℝ)⁻¹) := by
    have hb : (3 : ℝ)^(-3 : ℝ) = 1/27 := by norm_num [Real.rpow_neg, Real.rpow_natCast]
    rw [← hb, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  rw [he]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  simpa only [one_div] using h

theorem native_history_C0_real : 1-(3 : ℝ)^(-1/4 : ℝ) < (nativeC0 : ℝ) := by
  have h := ASDExplicitGamma.Numerics.Inverse.inv_root_lower
    (x := (1/3 : ℚ)) (l := 1-nativeC0) (n := 4)
    (by decide +kernel) (by decide) native_history_constants.2.1
  have he : (3 : ℝ)^(-1/4 : ℝ) = (1/3 : ℝ)^((4 : ℝ)⁻¹) := by
    have hb : (3 : ℝ)^(-1 : ℝ) = 1/3 := by norm_num [Real.rpow_neg]
    rw [← hb, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  rw [he]
  norm_num only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

end ASDExplicitGamma.Numerics.Native

module

public import ASDExplicitGamma.Numerics.Cold.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact algebraic certificates for the fractional powers used by the cold interval replay. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

noncomputable def coldAlphaReal : ℝ := Real.rpow 3 (-(1 / 4 : ℝ))
noncomputable def coldBetaReal : ℝ := Real.rpow 3 (-(3 / 20 : ℝ))

theorem coldAlpha_fourth_power : coldAlphaReal ^ 4 = 1 / 3 := by
  change ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 3
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem coldBeta_twentieth_power : coldBetaReal ^ 20 = 1 / 27 := by
  change ((3 : ℝ) ^ (-(3 / 20 : ℝ))) ^ 20 = 1 / 27
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem coldAlphaLower_power : coldAlphaLower ^ 4 ≤ (1 / 3 : ℚ) := by
  norm_num [coldAlphaLower]

theorem coldAlphaUpper_power : (1 / 3 : ℚ) ≤ coldAlphaUpper ^ 4 := by
  norm_num [coldAlphaUpper]

theorem coldBetaLower_power : coldBetaLower ^ 20 ≤ (1 / 27 : ℚ) := by
  norm_num [coldBetaLower]

theorem coldBetaUpper_power : (1 / 27 : ℚ) ≤ coldBetaUpper ^ 20 := by
  norm_num [coldBetaUpper]

theorem coldAlpha_interval_sound :
    (coldAlphaLower : ℝ) ≤ coldAlphaReal ∧ coldAlphaReal ≤ coldAlphaUpper := by
  have hlo : (coldAlphaLower : ℝ) ^ 4 ≤ coldAlphaReal ^ 4 := by
    rw [coldAlpha_fourth_power]
    have hc : ((coldAlphaLower ^ 4 : ℚ) : ℝ) ≤ ((1/3 : ℚ) : ℝ) := by
      exact_mod_cast coldAlphaLower_power
    simpa using hc
  have hhi : coldAlphaReal ^ 4 ≤ (coldAlphaUpper : ℝ) ^ 4 := by
    rw [coldAlpha_fourth_power]
    have hc : ((1/3 : ℚ) : ℝ) ≤ ((coldAlphaUpper ^ 4 : ℚ) : ℝ) := by
      exact_mod_cast coldAlphaUpper_power
    simpa using hc
  constructor
  · exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hlo
  · exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num [coldAlphaUpper]) hhi

theorem coldBeta_interval_sound :
    (coldBetaLower : ℝ) ≤ coldBetaReal ∧ coldBetaReal ≤ coldBetaUpper := by
  have hlo : (coldBetaLower : ℝ) ^ 20 ≤ coldBetaReal ^ 20 := by
    rw [coldBeta_twentieth_power]
    have hc : ((coldBetaLower ^ 20 : ℚ) : ℝ) ≤ ((1/27 : ℚ) : ℝ) := by
      exact_mod_cast coldBetaLower_power
    simpa using hc
  have hhi : coldBetaReal ^ 20 ≤ (coldBetaUpper : ℝ) ^ 20 := by
    rw [coldBeta_twentieth_power]
    have hc : ((1/27 : ℚ) : ℝ) ≤ ((coldBetaUpper ^ 20 : ℚ) : ℝ) := by
      exact_mod_cast coldBetaUpper_power
    simpa using hc
  constructor
  · exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by norm_num) _) hlo
  · exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num [coldBetaUpper]) hhi

end ASDExplicitGamma.Numerics.Cold

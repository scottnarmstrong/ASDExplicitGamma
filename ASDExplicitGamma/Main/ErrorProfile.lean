module

public import ASDExplicitGamma.Main.ErrorExpansion
public import ASDExplicitGamma.Main.RadicalSupport
import Mathlib.Tactic.FinCases

/-! Concavity and supporting lines of the full literal main error. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set

/-- The history denominator is positive for the source weak-history ratio. -/
theorem mainHd_nonneg {H : ℝ} (hH : 0 ≤ H) : 0 ≤ mainHd H := by
  have ha : mainAlpha < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact div_nonneg hH (sub_pos.mpr ha).le

/-- The source admissible interval supplies every radicand sign. -/
theorem mainError_interval_domain (a H xi : ℝ) (hH : 0 ≤ H) :
    Icc 0 (min a (xi/mainBetaOld)) ⊆ mainRadicalDomain (mainErrorOffsets a H xi) mainErrorRates := by
  intro f hf i
  have haf : 0 ≤ a-f := sub_nonneg.mpr (hf.2.trans (min_le_left _ _))
  have hxi : 0 ≤ xi-mainBetaOld*f := by
    have hbo : 0 < mainBetaOld := by norm_num [mainBetaOld]
    have h := (le_div_iff₀ hbo).mp (hf.2.trans (min_le_right _ _))
    nlinarith only [h]
  have hHd := mainHd_nonneg hH
  have hb : 0 ≤ mainBeta := by norm_num [mainBeta]
  have he : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
  change 0 ≤ mainErrorOffsets a H xi i - mainErrorRates i * f
  fin_cases i <;> norm_num [mainErrorOffsets, mainErrorRates]
  · have h := add_nonneg (mul_nonneg hb haf) (mul_nonneg he hHd)
    nlinarith only [h]
  · have h := add_nonneg (mul_nonneg (sq_nonneg mainBeta) haf)
      (mul_nonneg (show 0 ≤ 2*mainBeta*mainEpsNew+mainEpsNew^2 by positivity) hHd)
    nlinarith only [h]
  · exact sub_nonneg.mp hxi

/-- The literal rate vector is positive. -/
theorem mainErrorRates_pos (i : Fin 3) : 0 < mainErrorRates i := by
  fin_cases i <;> norm_num [mainErrorRates, mainBeta, mainBetaOld]

/-- The affine part alone gives a strictly negative derivative when the
source shell clock is positive. -/
theorem mainErrorSlope_pos {v : ℝ} (hv : 0 < v) : 0 < mainErrorSlope v := by
  unfold mainErrorSlope
  exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hv (by norm_num)) (by norm_num [mainBeta]))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

end ASDExplicitGamma.Main

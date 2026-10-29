module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Molecular startup algebra -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

/-- NU-SC-UPPER-STARTUP, the exact elementary startup inequality. -/
theorem molecular_startup_inequality {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x / 2) ^ 2 ≤ 1 + 5 * x / 4 := by
  have h := mul_nonneg hx (sub_nonneg.mpr hx1)
  nlinarith only [h]

/-- Algebraic helper for the molecular `5/4` estimate. The molecular upper
bound is an explicit hypothesis of this helper, not a source-node premise. -/
theorem molecular_five_four_of_upper {nu B sigma : ℝ}
    (hnu : 0 < nu) (hB : 0 ≤ B) (hBnu : B ≤ nu ^ 2)
    (hsigma : 0 ≤ sigma) (hupper : sigma ≤ nu + B / (2 * nu)) :
    sigma ^ 2 ≤ nu ^ 2 + 5 * B / 4 := by
  have hden : 0 < 2 * nu := mul_pos (by norm_num) hnu
  have hmul : sigma * (2 * nu) ≤ nu * (2 * nu) + B := by
    have h := (le_div_iff₀ hden).mp
      (show sigma ≤ (nu * (2 * nu) + B) / (2 * nu) by
        calc
          sigma ≤ nu + B / (2 * nu) := hupper
          _ = _ := by field_simp)
    exact h
  have hsq := mul_self_le_mul_self (mul_nonneg hsigma hden.le) hmul
  have hprod := mul_nonneg hB (sub_nonneg.mpr hBnu)
  have hnu2 : 0 < nu ^ 2 := sq_pos_of_pos hnu
  nlinarith only [hsq, hprod, hnu2]

end ASDExplicitGamma.Scalar

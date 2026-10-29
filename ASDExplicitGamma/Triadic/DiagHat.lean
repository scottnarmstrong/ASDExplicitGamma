module

public import ASDExplicitGamma.Triadic.PoincareCell
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Tensor hat functions for the DIAG nodal-average interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators

noncomputable section

/-- The unit mesh hat, including its zero extension. -/
def diagHat (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem diagHat_nonneg (t : ℝ) : 0 ≤ diagHat t := le_max_left _ _

theorem diagHat_le_one (t : ℝ) : diagHat t ≤ 1 := by
  unfold diagHat
  exact max_le zero_le_one (sub_le_self _ (abs_nonneg _))

theorem diagHat_continuous : Continuous diagHat := by
  unfold diagHat
  fun_prop

theorem diagHat_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : diagHat t = 0 :=
  max_eq_left (sub_nonpos.mpr ht)

@[simp] theorem diagHat_zero : diagHat 0 = 1 := by norm_num [diagHat]

/-- On one mesh interval, only the hats at its two ends contribute. -/
theorem diagHat_on_unit {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    diagHat t = 1 - t ∧ diagHat (t - 1) = t := by
  constructor
  · rw [diagHat, abs_of_nonneg ht.1, max_eq_right (sub_nonneg.mpr ht.2)]
  · rw [diagHat, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    have : 1 - -(t - 1) = t := by ring
    rw [this, max_eq_right ht.1]

/-- A unit hat is affine on either side of its vertex. -/
theorem diagHat_left {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 0) :
    diagHat t = 1 + t := by
  rw [diagHat, abs_of_nonpos ht.2, sub_neg_eq_add,
    max_eq_right (by linarith only [ht.1])]

end

end ASDExplicitGamma.Triadic

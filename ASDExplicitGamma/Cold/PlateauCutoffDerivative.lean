module

public import ASDExplicitGamma.Cold.PlateauCutoff
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Sharp Lipschitz and Euclidean derivative bounds for the plateau cutoff -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open MeasureTheory Set
open scoped Topology

/-- The maximum distance to the center is 1-Lipschitz for the spatial sup norm. -/
theorem plateau_center_radius_lipschitz :
    LipschitzWith 1 (fun x : Fin 2 → ℝ => max |x 0 - 1 / 2| |x 1 - 1 / 2|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  all_goals
    apply (abs_abs_sub_abs_le_abs_sub _ _).trans
    simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs, dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (x - y) _

/-- The sharp global Lipschitz constant, before restriction to the square. -/
theorem lipschitzWith_plateauCutoff : LipschitzWith (48 / 7) plateauCutoff := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hmax := plateau_center_radius_lipschitz.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hmax
  have hmin := abs_min_sub_min_le_max (2 * plateauSquareDepth x) 1
    (2 * plateauSquareDepth y) 1
  have heq : 2 * plateauSquareDepth x - 2 * plateauSquareDepth y =
      -4 * (max |x 0 - 1 / 2| |x 1 - 1 / 2| - max |y 0 - 1 / 2| |y 1 - 1 / 2|) := by
    unfold plateauSquareDepth; ring
  simp only [sub_self, abs_zero, heq, abs_mul, abs_neg] at hmin
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hmin
  rw [max_eq_left (mul_nonneg (by norm_num) (abs_nonneg _))] at hmin
  have hout : plateauCutoff x - plateauCutoff y = (12 / 7 : ℝ) *
      (min (2 * plateauSquareDepth x) 1 - min (2 * plateauSquareDepth y) 1) := by
    unfold plateauCutoff; ring
  simp only [Real.dist_eq, hout, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 12 / 7), NNReal.coe_div,
    NNReal.coe_ofNat]
  nlinarith only [hmin, hmax]

end ASDExplicitGamma.Cold

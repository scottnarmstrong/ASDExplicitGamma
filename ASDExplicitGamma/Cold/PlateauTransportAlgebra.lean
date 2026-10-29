module

public import ASDExplicitGamma.Cold.ResidualAxialAlgebra

/-! # Exact constants and Young inequalities in the plateau transport assembly -/

@[expose] public section

namespace ASDExplicitGamma.Cold

/-- The residual/residual entry is below the rational source margin. -/
theorem plateau_residual_entry_le : (48 : ℝ) / (7 * Real.sqrt 2 * Real.pi) ≤ 80 / 49 := by
  have hs : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [this, Real.sqrt_nonneg (2 : ℝ)]
  have hp := Real.pi_gt_three
  have hden : 0 < 7 * Real.sqrt 2 * Real.pi := by positivity
  apply (div_le_iff₀ hden).mpr
  have hmul : (7 / 5 : ℝ) * 3 ≤ Real.sqrt 2 * Real.pi :=
    mul_le_mul hs hp.le (by norm_num) (Real.sqrt_nonneg _)
  nlinarith only [hmul]

/-- The source fine/fine plus top/fine charge rounds upward to exactly seven. -/
theorem plateau_fine_constant_le :
    (96 : ℝ) / (7 * Real.pi) + 1152 / (49 * Real.pi ^ 2) ≤ 7 := by
  have hden : 0 < 49 * Real.pi ^ 2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  nlinarith [Real.pi_gt_d2, sq_nonneg (Real.pi - (31 / 10 : ℝ))]

/-- The top/top two-by-two block is paid by the full two gradient energies. -/
theorem plateau_top_block_le {x0 x1 y0 y1 b m : ℝ}
    (hb : b ^ 2 = 17 / 49) (hm : m ≤ 80 / 49)
    (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) :
    x0 * y0 + b * (x0 * y1 + x1 * y0) + m * x1 * y1 ≤
      (x0 ^ 2 + x1 ^ 2) + (y0 ^ 2 + y1 ^ 2) := by
  have hm' : m * x1 * y1 ≤ (80 / 49 : ℝ) * x1 * y1 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hx1) hy1
  nlinarith only [hm', sq_nonneg (x0 - y0), sq_nonneg (x0 - b * y1),
    sq_nonneg (b * x1 - y0), sq_nonneg (x1 - y1), sq_nonneg x1, sq_nonneg y1,
    mul_nonneg (sq_nonneg b) (sq_nonneg x1), mul_nonneg (sq_nonneg b) (sq_nonneg y1), hb]

/-- The exact Young parameter `1/4` in the source transport assembly. -/
theorem plateau_top_fine_young {V R D : ℝ} (hV : 0 ≤ V) (hR : 0 ≤ R) :
    2 * D * Real.sqrt (V * R) ≤ V / 4 + 4 * D ^ 2 * R := by
  rw [Real.sqrt_mul hV]
  nlinarith only [sq_nonneg (Real.sqrt V / 2 - 2 * D * Real.sqrt R),
    Real.sq_sqrt hV, Real.sq_sqrt hR]

/-- The complete source assembly before the martingale telescope. -/
theorem plateau_transport_assembly {T V R : ℝ} (hV : 0 ≤ V) (hR : 0 ≤ R)
    (hT : |T| ≤ V + (48 / (7 * Real.pi * Real.sqrt 8)) * Real.sqrt (V * R) +
      (48 / (7 * Real.pi)) * R) :
    2 * |T| ≤ (9 / 4 : ℝ) * V + 7 * R := by
  have hy := plateau_top_fine_young (D := 48 / (7 * Real.pi * Real.sqrt 8)) hV hR
  have hs : (48 / (7 * Real.pi * Real.sqrt 8)) ^ 2 = 288 / (49 * Real.pi ^ 2) := by
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  rw [hs] at hy
  have hc := mul_le_mul_of_nonneg_right plateau_fine_constant_le hR
  have heq : (96 : ℝ) / (7 * Real.pi) + 1152 / (49 * Real.pi ^ 2) =
      2 * (48 / (7 * Real.pi)) + 4 * (288 / (49 * Real.pi ^ 2)) := by ring
  rw [heq] at hc
  linarith only [hT, hy, hc]

end ASDExplicitGamma.Cold

module

public import ASDExplicitGamma.Numerics.Cold.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Ring

/-! # The explicit plateau weights and their tails

`plateauEvenWeight k` is the source weight at the even depth `r = 2(k+1)`.
Thus the tail at `j = 2J` is indexed by `k+J`; its geometric formula requires
`1 ≤ J`, exactly the corrected range `2 ≤ j`.
-/

@[expose] public section

namespace ASDExplicitGamma.Cold

/-- The transport weight at even depth `2(k+1)`. -/
noncomputable def plateauEvenWeight (k : ℕ) : ℝ :=
  if k = 0 then 53 / 72 else 28 * (1 / 9 : ℝ) ^ (k + 1)

/-- All source transport weights are nonnegative. -/
theorem plateauEvenWeight_nonneg (k : ℕ) : 0 ≤ plateauEvenWeight k := by
  unfold plateauEvenWeight
  split_ifs
  · norm_num
  · exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)

/-- The complete geometric weighted tail, valid only beyond the exceptional
first weight. Taking b=1, 3, or √3 gives the three source series. -/
theorem plateau_weighted_tail {J : ℕ} (hJ : 1 ≤ J) {b : ℝ}
    (hb : ‖b / 9‖ < 1) :
    (∑' k : ℕ, plateauEvenWeight (k + J) * b ^ (k + J + 1)) =
      28 * (b / 9) ^ (J + 1) / (1 - b / 9) := by
  have hfun : (fun k : ℕ => plateauEvenWeight (k + J) * b ^ (k + J + 1)) =
      fun k : ℕ => (28 * (b / 9) ^ (J + 1)) * (b / 9) ^ k := by
    funext k
    have hk : k + J ≠ 0 := by omega
    rw [plateauEvenWeight, ite_eq_right hk]
    have hprod : (1 / 9 : ℝ) ^ (k + J + 1) * b ^ (k + J + 1) =
        (b / 9) ^ (k + J + 1) := by
      rw [← mul_pow]
      congr 1
      ring
    rw [mul_assoc, hprod, show k + J + 1 = (J + 1) + k by omega, pow_add]
    ring
  rw [hfun, tsum_mul_left, tsum_geometric_of_norm_lt_one hb]
  simp only [div_eq_mul_inv]

/-- The unweighted tail beyond every even depth j≥2. -/
theorem plateau_tail {J : ℕ} (hJ : 1 ≤ J) :
    (∑' k : ℕ, plateauEvenWeight (k + J)) = (7 / 2 : ℝ) * (1 / 9 : ℝ) ^ J := by
  have h := plateau_weighted_tail hJ (b := 1) (by norm_num)
  simp only [one_pow, mul_one, one_div] at h
  rw [h, pow_succ]
  norm_num
  ring

/-- Summability of the source weights. -/
theorem summable_plateauEvenWeight : Summable plateauEvenWeight := by
  have htail : Summable (fun k : ℕ => plateauEvenWeight (k + 1)) := by
    have hgeo := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 9 : ℝ)‖ < 1)).mul_left
      ((28 : ℝ) * (1 / 9 : ℝ) ^ 2)
    convert hgeo using 1
    funext k
    rw [plateauEvenWeight, ite_eq_right (by omega), show k + 1 + 1 = 2 + k by omega, pow_add]
    ring
  exact (summable_nat_add_iff 1).mp htail

/-- Summability of the weights multiplied by 3^(r/2). -/
theorem summable_plateauEvenWeight_three :
    Summable (fun k : ℕ => plateauEvenWeight k * (3 : ℝ) ^ (k + 1)) := by
  apply (summable_nat_add_iff 1).mp
  have hgeo := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)).mul_left
    ((28 : ℝ) * (1 / 3 : ℝ) ^ 2)
  convert hgeo using 1
  funext k
  rw [plateauEvenWeight, ite_eq_right (by omega)]
  have hpow : (1 / 9 : ℝ) ^ (k + 1 + 1) * (3 : ℝ) ^ (k + 1 + 1) =
      (1 / 3 : ℝ) ^ (k + 1 + 1) := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, hpow, show k + 1 + 1 = 2 + k by omega, pow_add]
  ring

/-- The total transport mass weighted by 3^(r/2) is exactly 55/8. -/
theorem tsum_plateauEvenWeight_three :
    (∑' k : ℕ, plateauEvenWeight k * (3 : ℝ) ^ (k + 1)) = 55 / 8 := by
  rw [summable_plateauEvenWeight_three.tsum_eq_zero_add]
  have h := plateau_weighted_tail (by omega : 1 ≤ 1) (b := 3) (by norm_num)
  rw [h]
  norm_num [plateauEvenWeight]

/-- The 3^(r/4)-weighted tail beyond every even j≥2. -/
theorem plateau_sqrtThree_tail {J : ℕ} (hJ : 1 ≤ J) :
    (∑' k : ℕ, plateauEvenWeight (k + J) * (Real.sqrt 3) ^ (k + J + 1)) =
      28 * (Real.sqrt 3 / 9) ^ (J + 1) / (1 - Real.sqrt 3 / 9) := by
  apply plateau_weighted_tail hJ
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))]
  have hs := Numerics.Cold.sqrtThree_lt_twentySixOverFifteen
  linarith only [hs]

/-- The rational geometric-tail ratio used by the numerical cold certificate. -/
theorem plateau_sqrtThree_ratio_le : Real.sqrt 3 / 9 ≤ (26 / 135 : ℝ) := by
  calc
    Real.sqrt 3 / 9 ≤ (26 / 15 : ℝ) / 9 :=
      div_le_div_of_nonneg_right Numerics.Cold.sqrtThree_lt_twentySixOverFifteen.le
        (by norm_num)
    _ = _ := by norm_num

end ASDExplicitGamma.Cold

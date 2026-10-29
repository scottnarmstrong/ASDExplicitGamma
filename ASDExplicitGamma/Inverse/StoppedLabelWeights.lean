module

public import ASDExplicitGamma.Inverse.StoppedCorrelatedGroups
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! The literal source masses for arbitrary dependence between positive labels. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

/-- The source inter-label ratio is 3^(-1/2). -/
def labelWeightRatio : ℝ := (Real.sqrt 3)⁻¹

/-- Positive label n+1 receives half of the normalized geometric mass. -/
def positiveLabelWeight (n : ℕ) : ℝ :=
  (1/2:ℝ)*(1-labelWeightRatio)*labelWeightRatio^n

theorem label_weight_ratio_pos : 0 < labelWeightRatio := by
  unfold labelWeightRatio
  positivity

theorem label_weight_ratio_lt_one : labelWeightRatio < 1 := by
  unfold labelWeightRatio
  apply (inv_lt_one₀ (by positivity : (0:ℝ) < Real.sqrt 3)).mpr
  exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by norm_num)

theorem positive_label_weight_pos (n : ℕ) : 0 < positiveLabelWeight n :=
  mul_pos (mul_pos (by norm_num) (sub_pos.mpr label_weight_ratio_lt_one))
    (pow_pos label_weight_ratio_pos n)

/-- Every finite label population leaves the exact unused tail mass. -/
theorem positive_label_partial_sum (N : ℕ) :
    ∑ n ∈ Finset.range N, positiveLabelWeight n = (1/2:ℝ)*(1-labelWeightRatio^N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold positiveLabelWeight
    rw [pow_succ]
    ring

end
end ASDExplicitGamma.Inverse

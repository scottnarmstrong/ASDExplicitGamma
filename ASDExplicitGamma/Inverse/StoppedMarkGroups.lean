module

public import ASDExplicitGamma.Inverse.StoppedLabelWeights
public import Mathlib.Algebra.BigOperators.Fin

/-! The exact two-parity, nine-residue, finite-label masses, with unused tail retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

/-- Two local parity classes, nine classes for each positive label, and one
unused tail group. This is a deterministic finite population. -/
abbrev MarkGroup (N : ℕ) := Option (Fin 2 ⊕ (Fin N × Fin 9))

/-- The spare group's zero field retains exactly the unused infinite tail mass. -/
def markGroupWeight (N : ℕ) : MarkGroup N → ℝ
  | none => (1/2:ℝ)*labelWeightRatio^N
  | some (.inl _) => 1/4
  | some (.inr p) => positiveLabelWeight p.1.val/9

theorem mark_group_weight_pos (N : ℕ) (g : MarkGroup N) : 0 < markGroupWeight N g := by
  cases g with
  | none => exact mul_pos (by norm_num) (pow_pos label_weight_ratio_pos N)
  | some g =>
    cases g with
    | inl i => norm_num [markGroupWeight]
    | inr p => exact div_pos (positive_label_weight_pos p.1.val) (by norm_num)

/-- At each finite truncation the source masses sum to exactly one, so the
correlated-group convexity bound is applicable with no limiting hypothesis. -/
theorem mark_group_weights_sum (N : ℕ) : ∑ g : MarkGroup N, markGroupWeight N g = 1 := by
  have hsum : (∑ n : Fin N, positiveLabelWeight n.val) = (1/2:ℝ)*(1-labelWeightRatio^N) := by
    rw [Fin.sum_univ_eq_sum_range positiveLabelWeight N]
    exact positive_label_partial_sum N
  simp only [MarkGroup,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_prod_type,
    markGroupWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  simp only [mul_div_cancel₀ _ (by norm_num : (9:ℝ) ≠ 0)]
  rw [hsum]
  ring

end
end ASDExplicitGamma.Inverse

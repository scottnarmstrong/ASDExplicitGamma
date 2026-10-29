module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact dyadic-center chaining weights for the Gaussian tensor supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The center-to-child mesh lengths use these dyadic weights, starting at n=1. -/
noncomputable def supMeanDyadicWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- Exact finite mass and first moment of the dyadic chaining weights. -/
theorem supMean_dyadic_partial_sums (N : ℕ) :
    (∑ n ∈ Finset.range N, supMeanDyadicWeight n) = 1 - (1 / 2 : ℝ) ^ N ∧
    (∑ n ∈ Finset.range N, supMeanDyadicWeight n * (n + 1)) =
      2 - ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih.1, ih.2]
    simp only [supMeanDyadicWeight, pow_succ, Nat.cast_add, Nat.cast_one]
    constructor <;> ring

/-- Cauchy-Schwarz preserves the sharp square-root moment in every finite
center chain; replacing sqrt(n) by n would lose the source constant. -/
theorem supMean_dyadic_sqrt_partial_le (N : ℕ) :
    (∑ n ∈ Finset.range N, supMeanDyadicWeight n * Real.sqrt (n + 1)) ≤ Real.sqrt 2 := by
  have hw (n : ℕ) : 0 ≤ supMeanDyadicWeight n := by unfold supMeanDyadicWeight; positivity
  have hn (n : ℕ) : (0 : ℝ) ≤ n + 1 := by positivity
  have he (n : ℕ) : Real.sqrt (supMeanDyadicWeight n) *
      Real.sqrt (supMeanDyadicWeight n * (n + 1)) =
      supMeanDyadicWeight n * Real.sqrt (n + 1) := by
    rw [Real.sqrt_mul (hw n), ← mul_assoc, Real.mul_self_sqrt (hw n)]
  have hc := Real.sum_sqrt_mul_sqrt_le (s := Finset.range N) hw
    (fun n => mul_nonneg (hw n) (hn n))
  simp_rw [he] at hc
  obtain ⟨h0, h1⟩ := supMean_dyadic_partial_sums N
  rw [h0, h1] at hc
  have h0' : 1 - (1 / 2 : ℝ) ^ N ≤ 1 := sub_le_self _ (pow_nonneg (by norm_num) _)
  have h1' : 2 - ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ N ≤ 2 :=
    sub_le_self _ (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))
  exact hc.trans (by
    have h := mul_le_mul (Real.sqrt_le_sqrt h0') (Real.sqrt_le_sqrt h1')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [Real.sqrt_one, one_mul] using h)

end ASDExplicitGamma.Gaussian

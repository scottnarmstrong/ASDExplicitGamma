module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Pointwise binomial control used before the rare-factor expectation expansion. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open scoped BigOperators

/-- The non-leading terms in the order-`k` binomial expansion of a rare factor. -/
def rareExpansionTail (beta R X : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, (Nat.choose k i : ℝ) * beta ^ (k - i) * R ^ i * X

/-- For the source orders zero through three, the tail is exactly the non-leading
part of the binomial expansion. -/
theorem rare_expansion_binomial (beta R X : ℝ) (k : ℕ) (hk : k ≤ 3) :
    (beta + R) ^ k * X = beta ^ k * X + rareExpansionTail beta R X k := by
  unfold rareExpansionTail
  interval_cases k <;> norm_num [Finset.sum_Icc_succ_top] <;> ring

/-- If a nonnegative rare factor is bounded by `beta + R`, its `k`th power
times a nonnegative observable is bounded by the leading term and the rare
binomial tail. -/
theorem rare_factor_pointwise_expansion (B beta R X : ℝ) (k : ℕ)
    (hB : 0 ≤ B) (hX : 0 ≤ X)
    (hbound : B ≤ beta + R) (hk : k ≤ 3) :
    B ^ k * X ≤ beta ^ k * X + rareExpansionTail beta R X k := by
  rw [← rare_expansion_binomial beta R X k hk]
  apply mul_le_mul_of_nonneg_right _ hX
  exact pow_le_pow_left₀ hB (hbound) k

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicSquare
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact summation of the source dyadic mean and sharp fluctuation payments. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

def supMeanDyadicMeanScale (n : ℕ) : ℝ := supMeanDyadicWeight n/2

def supMeanDyadicMetricScale (n : ℕ) : ℝ := Real.sqrt 2*supMeanDyadicWeight n/2

/-- The complete expected refinement payment, with its separate mean and metric costs. -/
def supMeanDyadicIncrementPayment (T E : ℝ) (n : ℕ) : ℝ :=
  T*supMeanDyadicMeanScale n+2*E*supMeanDyadicMetricScale n*Real.sqrt (Real.log 2)*Real.sqrt (n+1:ℝ)

theorem supMean_dyadic_mean_scale_eq (n : ℕ) :
    supMeanDyadicMeanScale n = 1/(2:ℝ)^(n+2) := by
  unfold supMeanDyadicMeanScale supMeanDyadicWeight
  simp only [div_pow, one_pow, show n+2 = (n+1)+1 by omega, pow_succ]
  ring

theorem supMean_dyadic_metric_scale_eq (n : ℕ) :
    supMeanDyadicMetricScale n = Real.sqrt 2/(2:ℝ)^(n+2) := by
  calc
    _ = Real.sqrt 2*supMeanDyadicMeanScale n := by unfold supMeanDyadicMetricScale supMeanDyadicMeanScale; ring
    _ = _ := by rw [supMean_dyadic_mean_scale_eq]; ring

/-- Summing the actual half-cell payments gives exactly T/2+2 sqrt(log 2) E. -/
theorem supMean_dyadic_payment_sum_le (T E : ℝ) (hT : 0 ≤ T) (hE : 0 ≤ E) (N : ℕ) :
    (∑ n ∈ Finset.range N, supMeanDyadicIncrementPayment T E n) ≤
      T/2+2*Real.sqrt (Real.log 2)*E := by
  have hw : (∑ n ∈ Finset.range N, supMeanDyadicWeight n) ≤ 1 := by
    rw [(supMean_dyadic_partial_sums N).1]
    exact sub_le_self _ (by positivity)
  have hs := supMean_dyadic_sqrt_partial_le N
  have he (n : ℕ) : supMeanDyadicIncrementPayment T E n =
      (T/2)*supMeanDyadicWeight n+
        (Real.sqrt 2*E*Real.sqrt (Real.log 2))*(supMeanDyadicWeight n*Real.sqrt (n+1:ℝ)) := by
    unfold supMeanDyadicIncrementPayment supMeanDyadicMeanScale supMeanDyadicMetricScale
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ (T/2)*1+(Real.sqrt 2*E*Real.sqrt (Real.log 2))*Real.sqrt 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hw (by positivity))
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = T/2+(Real.sqrt 2)^2*(Real.sqrt (Real.log 2)*E) := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring

end
end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicSquare
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact logarithmic cardinality payments for every dyadic-center refinement. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- Every non-root center grid has at least four points. -/
theorem supMean_dyadic_child_card_ge_two (n : ℕ) : 2 ≤ Fintype.card (SupMeanDyadicIndex (n+1)) := by
  rw [supMean_dyadic_card, pow_succ]
  have hp : 1 ≤ (4:ℕ)^n := pow_pos (by decide : 0 < (4:ℕ)) n
  omega

/-- The exact Gaussian finite-maximum payment sqrt(2 log(4^(n+1))). -/
theorem supMean_dyadic_log_card_sqrt (n : ℕ) :
    Real.sqrt (2*Real.log (Fintype.card (SupMeanDyadicIndex (n+1)):ℝ)) =
      2*Real.sqrt (Real.log 2)*Real.sqrt (n+1:ℝ) := by
  have hlog : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [supMean_dyadic_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, h4]
  rw [show 2*(((n+1:ℕ):ℝ)*(2*Real.log 2)) = 4*Real.log 2*(n+1:ℝ) by push_cast; ring]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow,
    Real.sq_sqrt hlog, Real.sq_sqrt (by positivity : (0:ℝ) ≤ n+1)]
  ring

end ASDExplicitGamma.Gaussian

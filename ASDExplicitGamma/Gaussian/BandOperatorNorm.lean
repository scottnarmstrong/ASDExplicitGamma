module

public import ASDExplicitGamma.Gaussian.FiniteHilbertFactor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Squared operator bounds on the Hilbert direct sum of shells -/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

/-- Cauchy–Schwarz across independent input coordinates retains the sum of squared shell
operator bounds, rather than the square of the sum. -/
theorem finiteFactor_norm_sq_le {b : ℕ} (H : Fin b → Type*)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ∀ i, H i →L[ℝ] E) (C : Fin b → ℝ)
    (hT : ∀ i u, ‖T i u‖ ≤ C i * ‖u‖) (u : FiniteHilbert H) :
    ‖finiteFactor H T u‖ ^ 2 ≤ (∑ i, C i ^ 2) * ‖u‖ ^ 2 := by
  classical
  have hnorm : ‖finiteFactor H T u‖ ≤ ∑ i, C i * ‖u i‖ := by
    simp only [finiteFactor, sum_apply, ContinuousLinearMap.comp_apply]
    change ‖∑ i, T i (u i)‖ ≤ _
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hT i (u i))
  calc
    _ ≤ (∑ i, C i * ‖u i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ i, C i ^ 2) * ∑ i, ‖u i‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by rw [PiLp.norm_sq_eq_of_L2]

/-- The same sharp direct-sum bound as an operator norm estimate. -/
theorem finiteFactor_norm_le_sqrt {b : ℕ} (H : Fin b → Type*)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ∀ i, H i →L[ℝ] E) (C : Fin b → ℝ)
    (hT : ∀ i u, ‖T i u‖ ≤ C i * ‖u‖) :
    ‖finiteFactor H T‖ ≤ Real.sqrt (∑ i, C i ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact finiteFactor_norm_sq_le H T C hT u

end ASDExplicitGamma.Gaussian

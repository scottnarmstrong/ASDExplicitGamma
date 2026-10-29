module

public import ASDExplicitGamma.Gaussian.Finite
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! # Exact standard-normal even moments at arbitrary order

This generalizes the fixed fortieth-moment calculation in `MolecularMoments`.
-/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

private theorem normal_pow_polynomiallyBoundedDerivative (n : ℕ) :
    HasPolynomiallyBoundedDerivative (fun x : ℝ => x ^ (n + 1)) := by
  refine ⟨by fun_prop, (n : ℝ) + 2, by positivity, n + 1, ?_⟩
  intro x
  have hd : deriv (fun y : ℝ => y ^ (n + 1)) x = (n + 1 : ℕ) * x ^ n := by
    simp
  have hp : |x| ^ (n + 1) ≤ (1 + |x|) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) (by linarith [abs_nonneg x]) _
  have hpn : |x| ^ n ≤ (1 + |x|) ^ (n + 1) := by
    exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith [abs_nonneg x]) n).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x] : 1 ≤ 1 + |x|) (Nat.le_succ n))
  have hscaled := mul_le_mul_of_nonneg_left hpn (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
  have hc : |((n + 1 : ℕ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := abs_of_nonneg (by positivity)
  simp only [hd, abs_mul, abs_pow, hc]
  push_cast at hscaled ⊢
  nlinarith only [hp, hscaled]

theorem normal_even_moment_step (p : ℕ) :
    (∫ x : ℝ, x ^ (2 * (p + 1)) ∂gaussianReal 0 1) =
      (2 * p + 1 : ℕ) * ∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1 := by
  have hi := integral_id_mul_eq_integral_deriv_gaussianReal (normal_pow_polynomiallyBoundedDerivative (2 * p))
  have hp : (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x => x ^ (2 * (p + 1)) := by
    funext x
    rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega, pow_succ]
    ring
  have hd : (fun x : ℝ => deriv (fun y : ℝ => y ^ (2 * p + 1)) x) =
      fun x => ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) := by
    funext x
    simp
  rw [hp, hd, integral_const_mul] at hi
  exact hi

/-- Standard-normal even moments obey the elementary (2k)^k bound, including k = 0. -/
theorem normal_even_moment_le (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ≤ (2 * (k : ℝ)) ^ k := by
  have hb (j : ℕ) (hj : j ≤ k) :
      (∫ x : ℝ, x ^ (2 * j) ∂gaussianReal 0 1) ≤ (2 * (k : ℝ)) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [normal_even_moment_step]
      have hcoeff : (2 * j + 1 : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 2 * j + 1 ≤ 2 * k by omega)
      have hnonneg : (0 : ℝ) ≤ 2 * j + 1 := by positivity
      have hstep := mul_le_mul_of_nonneg_left (ih (by omega)) hnonneg
      have hscale := mul_le_mul_of_nonneg_right hcoeff (by positivity : (0 : ℝ) ≤ (2 * (k : ℝ)) ^ j)
      push_cast at hstep ⊢
      rw [pow_succ]
      nlinarith only [hstep, hscale]
  exact hb k le_rfl

/-- Gaussian IBP gives the exact odd double factorial, with the source integer convention. -/
theorem normal_even_moment_eq_doubleFactorial (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) = ((2 * k - 1)‼ : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using normal_even_moment_step 0
  | succ k hk ih =>
    rw [normal_even_moment_step, ih]
    have he : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
    have hc : (2 * k - 1 + 2 : ℕ) = 2 * k + 1 := by omega
    rw [he, Nat.doubleFactorial_add_two, hc]
    push_cast
    rfl

end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact finite Gaussian moments used by the product and second-chaos estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

/-- Every monomial and its derivative obey a common polynomial growth bound. -/
theorem gaussian_monomial_derivative_bound (n : ℕ) :
    Gaussian.HasPolynomiallyBoundedDerivative (fun x : ℝ => x^(n+1)) := by
  refine ⟨by fun_prop, (n:ℝ)+2,by positivity,n+1,?_⟩
  intro x
  have hbase : 1 ≤ 1+|x| := le_add_of_nonneg_right (abs_nonneg x)
  have h0 : |x|^(n+1) ≤ (1+|x|)^(n+1) :=
    pow_le_pow_left₀ (abs_nonneg x) (by linarith only) _
  have h1 : |x|^n ≤ (1+|x|)^(n+1) :=
    (pow_le_pow_left₀ (abs_nonneg x) (by linarith only) n).trans
      (pow_le_pow_right₀ hbase (Nat.le_succ n))
  have hd := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (n:ℝ)+1)
  simp only [deriv_pow_field,Nat.add_sub_cancel,abs_mul,abs_pow,Nat.cast_add,Nat.cast_one,
    abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)]
  nlinarith only [h0,hd]

noncomputable def standardGaussianMoment (n : ℕ) : ℝ := ∫ x : ℝ, x^n ∂gaussianReal 0 1

/-- Gaussian integration by parts gives the exact moment recursion. -/
theorem standard_gaussian_moment_recursion (n : ℕ) :
    standardGaussianMoment (n+2) = ((n:ℝ)+1)*standardGaussianMoment n := by
  have h := Gaussian.integral_id_mul_eq_integral_deriv_gaussianReal
    (gaussian_monomial_derivative_bound n)
  have hl : (fun x : ℝ => x*x^(n+1)) = (fun x : ℝ => x^(n+2)) := by
    funext x
    simp only [pow_succ]
    ring
  rw [hl] at h
  simp only [deriv_pow_field,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,integral_const_mul] at h
  exact h

/-- The five even moments needed through degree eight, including the sharp chaos constant 15. -/
theorem standard_gaussian_even_moments :
    standardGaussianMoment 0 = 1 ∧ standardGaussianMoment 2 = 1 ∧
    standardGaussianMoment 4 = 3 ∧ standardGaussianMoment 6 = 15 ∧ standardGaussianMoment 8 = 105 := by
  have h0 : standardGaussianMoment 0 = 1 := by simp [standardGaussianMoment]
  have h2 := standard_gaussian_moment_recursion 0
  have h4 := standard_gaussian_moment_recursion 2
  have h6 := standard_gaussian_moment_recursion 4
  have h8 := standard_gaussian_moment_recursion 6
  norm_num at h2 h4 h6 h8
  exact ⟨h0,by linarith only [h0,h2],by linarith only [h0,h2,h4],
    by linarith only [h0,h2,h4,h6],by linarith only [h0,h2,h4,h6,h8]⟩

end ASDExplicitGamma.Scalar

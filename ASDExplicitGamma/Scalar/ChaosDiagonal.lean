module

public import ASDExplicitGamma.Scalar.ChaosDiagonalKernel

/-! Actual diagonal quadratic observables of independent standard Gaussian coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ASDExplicitGamma.Gaussian

noncomputable def diagonalGaussianChaos {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, a i*gaussianHermiteTwo i x

noncomputable def diagonalGaussianPolynomial {n : ℕ} (a : Fin n → ℝ) : GaussianPolynomial n :=
  (List.ofFn (fun i => [(a i,[i,i]),(-a i,[])])).flatten

theorem diagonal_gaussian_polynomial_eval {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) :
    gaussianPolynomialEval (diagonalGaussianPolynomial a) x = diagonalGaussianChaos a x := by
  unfold diagonalGaussianPolynomial diagonalGaussianChaos
  rw [gaussian_polynomial_eval_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [gaussianPolynomialEval,gaussianMonomial,gaussianHermiteTwo,pow_two]
  ring

theorem integrable_diagonal_gaussian_power {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    Integrable (fun x => (diagonalGaussianChaos a x)^k) (standardGaussianPi n) := by
  have h := integrable_gaussian_polynomial (gaussianPolynomialPow (diagonalGaussianPolynomial a) k)
  have he : gaussianPolynomialEval (gaussianPolynomialPow (diagonalGaussianPolynomial a) k) =
      fun x => (diagonalGaussianChaos a x)^k := by
    funext x
    rw [gaussian_polynomial_eval_pow,diagonal_gaussian_polynomial_eval]
  rw [he] at h
  exact h

end ASDExplicitGamma.Scalar

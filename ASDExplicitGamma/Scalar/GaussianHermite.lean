module

public import ASDExplicitGamma.Scalar.GaussianPolynomialIntegral

/-! Exact Hermite second-chaos kernels, computed using proved Gaussian Wick integration. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ASDExplicitGamma.Gaussian

noncomputable def gaussianHermiteTwo {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : ℝ := (x i)^2-1

noncomputable def gaussianHermiteTwoPolynomial {n : ℕ} (i : Fin n) : GaussianPolynomial n :=
  [(1,[i,i]),(-1,[])]

theorem gaussian_hermite_two_eval {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    gaussianPolynomialEval (gaussianHermiteTwoPolynomial i) x = gaussianHermiteTwo i x := by
  norm_num [gaussianPolynomialEval,gaussianHermiteTwoPolynomial,gaussianMonomial,gaussianHermiteTwo,pow_two]
  ring

/-- A centered Hermite coordinate has mean zero. -/
theorem gaussian_hermite_two_mean {n : ℕ} (i : Fin n) :
    (∫ x, gaussianHermiteTwo i x ∂standardGaussianPi n) = 0 := by
  have he : gaussianHermiteTwo i = gaussianPolynomialEval (gaussianHermiteTwoPolynomial i) := by
    funext x
    exact (gaussian_hermite_two_eval i x).symm
  rw [he,integral_gaussian_polynomial_eq_mean]
  norm_num [gaussianHermiteTwoPolynomial,gaussianPolynomialMean,gaussianWickValue,gaussianContractions]

/-- Orthogonality of the centered quadratic Hermite coordinates. -/
theorem gaussian_hermite_two_covariance {n : ℕ} (i j : Fin n) :
    (∫ x, gaussianHermiteTwo i x*gaussianHermiteTwo j x ∂standardGaussianPi n) =
      2*(if i=j then 1 else 0) := by
  have he : (fun x => gaussianHermiteTwo i x*gaussianHermiteTwo j x) =
      gaussianPolynomialEval (gaussianPolynomialMul (gaussianHermiteTwoPolynomial i)
        (gaussianHermiteTwoPolynomial j)) := by
    funext x
    simp only [gaussian_polynomial_eval_mul,gaussian_hermite_two_eval]
  rw [he,integral_gaussian_polynomial_eq_mean]
  by_cases hij : i=j
  · subst j
    norm_num [gaussianHermiteTwoPolynomial,gaussianPolynomialMean,gaussianPolynomialMul,
      gaussianWickValue,gaussianContractions]
  · norm_num [gaussianHermiteTwoPolynomial,gaussianPolynomialMean,gaussianPolynomialMul,
      gaussianWickValue,gaussianContractions,hij,Ne.symm hij]

noncomputable def gaussianHermiteFourthKernel {n : ℕ} (i j k l : Fin n) : ℝ :=
  gaussianPolynomialMean (gaussianPolynomialMul (gaussianHermiteTwoPolynomial i)
    (gaussianPolynomialMul (gaussianHermiteTwoPolynomial j)
      (gaussianPolynomialMul (gaussianHermiteTwoPolynomial k) (gaussianHermiteTwoPolynomial l))))

theorem gaussian_hermite_fourth_integral {n : ℕ} (i j k l : Fin n) :
    (∫ x, gaussianHermiteTwo i x*(gaussianHermiteTwo j x*(gaussianHermiteTwo k x*gaussianHermiteTwo l x))
      ∂standardGaussianPi n) = gaussianHermiteFourthKernel i j k l := by
  unfold gaussianHermiteFourthKernel
  rw [← integral_gaussian_polynomial_eq_mean]
  apply integral_congr_ae
  filter_upwards with x
  simp only [gaussian_polynomial_eval_mul,gaussian_hermite_two_eval]

/-- The complete diagonal Hermite quartic kernel, including all repeated-index patterns. -/
theorem gaussian_hermite_fourth_kernel {n : ℕ} (i j k l : Fin n) :
    gaussianHermiteFourthKernel i j k l =
      48*(if i=j ∧ i=k ∧ i=l then 1 else 0)+
      4*((if i=j ∧ k=l then 1 else 0)+(if i=k ∧ j=l then 1 else 0)+(if i=l ∧ j=k then 1 else 0)) := by
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hil : i=l <;>
    by_cases hjk : j=k <;> by_cases hjl : j=l <;> by_cases hkl : k=l <;>
    simp_all [gaussianHermiteFourthKernel,gaussianHermiteTwoPolynomial,gaussianPolynomialMean,
      gaussianPolynomialMul,gaussianWickValue,gaussianContractions] <;> norm_num

noncomputable def gaussianHermiteProductPolynomial {n : ℕ} : List (Fin n) → GaussianPolynomial n
  | [] => [(1,[])]
  | i::a => gaussianPolynomialMul (gaussianHermiteTwoPolynomial i) (gaussianHermiteProductPolynomial a)

theorem gaussian_hermite_product_eval {n : ℕ} (a : List (Fin n)) (x : Fin n → ℝ) :
    gaussianPolynomialEval (gaussianHermiteProductPolynomial a) x =
      (a.map (fun i => gaussianHermiteTwo i x)).prod := by
  induction a with
  | nil => norm_num [gaussianHermiteProductPolynomial,gaussianPolynomialEval,gaussianMonomial]
  | cons i a ih =>
    simp only [gaussianHermiteProductPolynomial,gaussian_polynomial_eval_mul,gaussian_hermite_two_eval,
      ih,List.map_cons,List.prod_cons]

theorem integrable_gaussian_hermite_product {n : ℕ} (a : List (Fin n)) :
    Integrable (fun x => (a.map (fun i => gaussianHermiteTwo i x)).prod) (standardGaussianPi n) := by
  have he : gaussianPolynomialEval (gaussianHermiteProductPolynomial a) =
      fun x => (a.map (fun i => gaussianHermiteTwo i x)).prod := by
    funext x
    exact gaussian_hermite_product_eval a x
  rw [← he]
  exact integrable_gaussian_polynomial _

end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.ChaosDiagonal

/-! Exact moments of the actual diagonal quadratic observable. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ASDExplicitGamma.Gaussian

/-- Weighted centered Hermite coordinates have zero mean. -/
theorem diagonal_gaussian_mean_zero {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, diagonalGaussianChaos a x ∂standardGaussianPi n) = 0 := by
  unfold diagonalGaussianChaos
  rw [integral_finsetSum _ (fun i _ => by
    have hi := integrable_gaussian_polynomial (gaussianHermiteTwoPolynomial i)
    have he : gaussianPolynomialEval (gaussianHermiteTwoPolynomial i) = gaussianHermiteTwo i := by
      funext x
      exact gaussian_hermite_two_eval i x
    rw [he] at hi
    exact hi.const_mul (a i))]
  simp only [integral_const_mul,gaussian_hermite_two_mean,mul_zero,Finset.sum_const_zero]

/-- The variance of a weighted diagonal Gaussian quadratic is twice the squared coefficient norm. -/
theorem diagonal_gaussian_second_moment {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, (diagonalGaussianChaos a x)^2 ∂standardGaussianPi n) = 2*∑ i, (a i)^2 := by
  have hInt (i j : Fin n) : Integrable (fun x => a i*a j*(gaussianHermiteTwo i x*gaussianHermiteTwo j x))
      (standardGaussianPi n) := by
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using
      (integrable_gaussian_hermite_product [i,j]).const_mul (a i*a j)
  have he (x : Fin n → ℝ) : (diagonalGaussianChaos a x)^2 =
      ∑ i, ∑ j, a i*a j*(gaussianHermiteTwo i x*gaussianHermiteTwo j x) := by
    simp only [diagonalGaussianChaos,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))]
  have hRow (i : Fin n) : (∫ x, ∑ j, a i*a j*(gaussianHermiteTwo i x*gaussianHermiteTwo j x)
      ∂standardGaussianPi n) = 2*(a i)^2 := by
    rw [integral_finsetSum _ (fun j _ => hInt i j)]
    simp only [integral_const_mul,gaussian_hermite_two_covariance,mul_ite,mul_zero,
      mul_one,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  simp_rw [hRow]
  rw [← Finset.mul_sum]

/-- The fourth moment retains exactly the disconnected and cyclic Wick contractions. -/
theorem diagonal_gaussian_fourth_moment {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, (diagonalGaussianChaos a x)^4 ∂standardGaussianPi n) =
      48*(∑ i, (a i)^4)+12*(∑ i, (a i)^2)^2 := by
  have hInt (i j k l : Fin n) : Integrable (fun x =>
      a i*a j*a k*a l*(gaussianHermiteTwo i x*(gaussianHermiteTwo j x*
        (gaussianHermiteTwo k x*gaussianHermiteTwo l x)))) (standardGaussianPi n) := by
    have hi := (integrable_gaussian_hermite_product [i,j,k,l]).const_mul (a i*a j*a k*a l)
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hi
  have he (x : Fin n → ℝ) : (diagonalGaussianChaos a x)^4 =
      ∑ i, ∑ j, ∑ k, ∑ l, a i*a j*a k*a l*(gaussianHermiteTwo i x*(gaussianHermiteTwo j x*
        (gaussianHermiteTwo k x*gaussianHermiteTwo l x))) := by
    simp only [diagonalGaussianChaos,pow_succ,pow_zero,one_mul,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, a i*a j*a k*a l*gaussianHermiteFourthKernel i j k l := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hInt i j k l))))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun l _ => hInt i j k l)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hInt i j k l))]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_finsetSum _ (fun l _ => hInt i j k l)]
      apply Finset.sum_congr rfl
      intro l _
      rw [integral_const_mul,gaussian_hermite_fourth_integral]
    _ = _ := diagonal_chaos_fourth_contractions a

/-- The sharp fourth/second moment comparison for actual diagonal second Gaussian chaos. -/
theorem diagonal_gaussian_fourth_le_fifteen {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, (diagonalGaussianChaos a x)^4 ∂standardGaussianPi n) ≤
      15*(∫ x, (diagonalGaussianChaos a x)^2 ∂standardGaussianPi n)^2 := by
  rw [diagonal_gaussian_fourth_moment,diagonal_gaussian_second_moment]
  have h := diagonal_fourth_le_square_sum a
  nlinarith only [h]

end ASDExplicitGamma.Scalar

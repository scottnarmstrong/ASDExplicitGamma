module

public import ASDExplicitGamma.Model.Q3CovDerivatives

/-! Actual covariance-derivative contractions of the product-q3 kernel. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- Genuine coordinate iterated derivatives of the literal two-dimensional covariance. -/
def q3CovariancePartial (a b : ℕ) (x y : ℝ) : ℝ :=
  iteratedDeriv a (fun t => iteratedDeriv b (fun u => q3ProductCovariance ![t,u]) y) x

 theorem q3CovariancePartial_eq (a b : ℕ) (x y : ℝ) :
    q3CovariancePartial a b x y = iteratedDeriv a q3Cov x*iteratedDeriv b q3Cov y := by
  simp only [q3CovariancePartial, q3ProductCovariance, Matrix.cons_val_zero, Matrix.cons_val_one,
    iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]

 theorem q3Cov_at_zero : q3Cov 0 = 1 := by
  have h := q3Cov_eq_polynomial_on_unit_interval 0 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The variance contraction of an actual n-th derivative component: the
sign accounts for derivatives in the second covariance argument. -/
def q3TensorComponentVariance {n : ℕ} (w : Fin n → Fin 2) : ℝ :=
  (-1:ℝ)^n*q3CovariancePartial (2*∑ a, if w a=0 then 1 else 0)
    (2*∑ a, if w a=1 then 1 else 0) 0 0

 theorem q3TensorComponentVariance_one (i : Fin 2) :
    q3TensorComponentVariance (fun _ : Fin 1 => i) = (q3PartialVarianceOne i : ℝ) := by
  fin_cases i <;> norm_num [q3TensorComponentVariance, q3CovariancePartial_eq,
    q3Cov_iteratedDeriv_values.1, iteratedDeriv_zero, q3Cov_at_zero,
    q3PartialVarianceOne, q3r1]

 theorem q3TensorComponentVariance_two (i j : Fin 2) :
    q3TensorComponentVariance ![i,j] = (q3PartialVarianceTwo (i,j) : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [q3TensorComponentVariance, Fin.sum_univ_two] <;>
    norm_num [q3CovariancePartial_eq,
    q3Cov_iteratedDeriv_values.1, q3Cov_iteratedDeriv_values.2.1, iteratedDeriv_zero, q3Cov_at_zero,
    Fin.sum_univ_two, q3PartialVarianceTwo, q3r1, q3r2]

 theorem q3TensorComponentVariance_three (i j k : Fin 2) :
    q3TensorComponentVariance ![i,j,k] = (q3PartialVarianceThree (i,j,k) : ℝ) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [q3TensorComponentVariance, Fin.sum_univ_succ] <;>
    norm_num [q3CovariancePartial_eq,
    q3Cov_iteratedDeriv_values.1, q3Cov_iteratedDeriv_values.2.1, q3Cov_iteratedDeriv_values.2.2,
    iteratedDeriv_zero, q3Cov_at_zero, Fin.sum_univ_succ, q3PartialVarianceThree, q3r1, q3r2, q3r3]

 theorem q3DerivativeVarianceTraces :
    (∑ i : Fin 2, q3TensorComponentVariance (fun _ : Fin 1 => i)) = (q3mu1 : ℝ) ∧
    (∑ i : Fin 2, ∑ j : Fin 2, q3TensorComponentVariance ![i,j]) = (q3mu2 : ℝ) ∧
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, q3TensorComponentVariance ![i,j,k]) = (q3mu3 : ℝ) := by
  simp only [q3TensorComponentVariance_one, q3TensorComponentVariance_two, q3TensorComponentVariance_three]
  norm_num [Fin.sum_univ_two, q3PartialVarianceOne, q3PartialVarianceTwo, q3PartialVarianceThree,
    q3mu1, q3mu2, q3mu3, q3r1, q3r2, q3r3]

/-- The squared Frobenius entries of the fixed planar skew matrix. -/
def q3SkewEntry (i j : Fin 2) : ℝ := if i=0 ∧ j=1 then -1 else if i=1 ∧ j=0 then 1 else 0

end
end ASDExplicitGamma.Model

module

public import ASDExplicitGamma.Scalar.ChaosDiagonalMoments
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Spectral transport of scalar Gaussian quadratic forms to independent Hermite coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def centeredGaussianQuadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A) x) - Matrix.trace A

theorem centered_gaussian_quadratic_spectral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : Fin n → ℝ) :
    centeredGaussianQuadratic A (∑ i, x i • hA.eigenvectorBasis i) =
      diagonalGaussianChaos hA.eigenvalues x := by
  have heig (i : Fin n) : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A) (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  unfold centeredGaussianQuadratic diagonalGaussianChaos gaussianHermiteTwo
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [map_sum,map_smul,heig,inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right]
  simp only [OrthonormalBasis.inner_eq_ite,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,Finset.sum_sub_distrib,mul_sub,pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every natural moment of a symmetric Gaussian quadratic is its actual diagonal moment. -/
theorem centered_gaussian_quadratic_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    (∫ x, (centeredGaussianQuadratic A x)^k ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ x, (diagonalGaussianChaos hA.eigenvalues x)^k ∂Gaussian.standardGaussianPi n := by
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i • hA.eigenvectorBasis i) := by fun_prop
  have hf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (centeredGaussianQuadratic A x)^k) := by
    unfold centeredGaussianQuadratic
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis,
    integral_map hm.aemeasurable hf.measurable.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  rw [centered_gaussian_quadratic_spectral]

/-- Polynomial powers of a centered Gaussian quadratic are genuinely integrable. -/
theorem integrable_centered_gaussian_quadratic_power {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    Integrable (fun x => (centeredGaussianQuadratic A x)^k) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i • hA.eigenvectorBasis i) := by fun_prop
  have hf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (centeredGaussianQuadratic A x)^k) := by
    unfold centeredGaussianQuadratic
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis,
    integrable_map_measure hf.measurable.aestronglyMeasurable hm.aemeasurable]
  have he : (fun x : Fin n → ℝ => (centeredGaussianQuadratic A (∑ i, x i • hA.eigenvectorBasis i))^k) =
      fun x => (diagonalGaussianChaos hA.eigenvalues x)^k := by
    funext x
    rw [centered_gaussian_quadratic_spectral]
  change Integrable (fun x : Fin n → ℝ => (centeredGaussianQuadratic A (∑ i, x i • hA.eigenvectorBasis i))^k) _
  rw [he]
  exact integrable_diagonal_gaussian_power _ _

theorem centered_gaussian_quadratic_mean_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    (∫ x, centeredGaussianQuadratic A x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  have h := centered_gaussian_quadratic_moment A hA 1
  simpa only [pow_one,diagonal_gaussian_mean_zero] using h

/-- Sharp scalar second-chaos moment bound for every symmetric quadratic coefficient. -/
theorem centered_gaussian_quadratic_fourth_le_fifteen {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (∫ x, (centeredGaussianQuadratic A x)^4 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      15*(∫ x, (centeredGaussianQuadratic A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  rw [centered_gaussian_quadratic_moment A hA 4,centered_gaussian_quadratic_moment A hA 2]
  exact diagonal_gaussian_fourth_le_fifteen _

end ASDExplicitGamma.Scalar

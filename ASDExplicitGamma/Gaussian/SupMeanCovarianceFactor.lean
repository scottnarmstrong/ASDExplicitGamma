module

public import ASDExplicitGamma.Gaussian.DerivativeLawFinite
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Finite covariance factors derived from the actual joint Gaussian law. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section

/-- The covariance matrix uses actual second moments of the centered observations. -/
def supMeanCovariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (X : Fin n → Ω → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, X i ω * X j ω ∂μ

/-- A finite Gaussian observation covariance is positive semidefinite, including
singular laws and repeated observations. -/
theorem supMean_covariance_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) : (supMeanCovariance μ X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change (∫ ω, X j ω * X i ω ∂μ) = ∫ ω, X i ω * X j ω ∂μ
    congr 1
    funext ω
    ring
  · intro t
    have hi (i j : Fin n) : Integrable (fun ω => t i * t j * (X i ω * X j ω)) μ :=
      ((hX.memLp i 2 (by simp)).integrable_mul (hX.memLp j 2 (by simp))).const_mul _
    have heq : star t ⬝ᵥ (supMeanCovariance μ X *ᵥ t) =
        ∫ ω, (∑ i, t i * X i ω)^2 ∂μ := by
      simp only [dotProduct, mulVec, supMeanCovariance, Pi.star_apply, star_trivial,
        Finset.mul_sum]
      rw [show (fun ω => (∑ i, t i * X i ω)^2) =
        (fun ω => ∑ i, ∑ j, t i * t j * (X i ω * X j ω)) by
          funext ω
          rw [pow_two, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
      simp only [integral_const_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    exact integral_nonneg fun ω => sq_nonneg _

/-- The canonical finite covariance factor; no realization premise is supplied. -/
def supMeanCovarianceFactor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (X : Fin n → Ω → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (supMeanCovariance μ X)

/-- The rows of the factor have precisely the actual covariance Gram matrix. -/
theorem supMean_covariance_factor_gram {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) (i j : Fin n) :
    (∑ k, supMeanCovarianceFactor μ X i k * supMeanCovarianceFactor μ X j k) =
      ∫ ω, X i ω * X j ω ∂μ := by
  have hpos : 0 ≤ supMeanCovariance μ X := (supMean_covariance_posSemidef μ X hX).nonneg
  have hs := CFC.sqrt_nonneg (supMeanCovariance μ X)
  have hherm : (supMeanCovarianceFactor μ X).IsHermitian := hs.posSemidef.isHermitian
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (CFC.sqrt_mul_sqrt_self (supMeanCovariance μ X) hpos)
  change (∑ k, supMeanCovarianceFactor μ X i k * supMeanCovarianceFactor μ X k j) = _ at he
  calc
    _ = ∑ k, supMeanCovarianceFactor μ X i k * supMeanCovarianceFactor μ X k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hherm.apply k j, star_trivial]
    _ = _ := he

end
end ASDExplicitGamma.Gaussian

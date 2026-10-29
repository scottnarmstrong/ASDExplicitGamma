module

public import ASDExplicitGamma.Gaussian.SupMeanLinearLaw
public import ASDExplicitGamma.Gaussian.SupMeanCovarianceFactor

/-! Equality of finite observation laws from their scalar Gaussian combinations. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- Scalar linear combinations determine the entire finite vector law. -/
theorem supMean_measure_eq_of_linear_laws {n : ℕ} (μ ν : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : Fin n → ℝ, μ.map (fun x => ∑ i, t i * x i) =
      ν.map (fun x => ∑ i, t i * x i)) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have heq : (L : (Fin n → ℝ) → ℝ) =
      (fun x => ∑ i, L (fun j => if i = j then 1 else 0) * x i) := by
    funext x
    simpa only [smul_eq_mul, mul_comm] using! L.toLinearMap.pi_apply_eq_sum_univ x
  rw [heq, h]

/-- The covariance factor reproduces every scalar combination's variance. -/
theorem supMean_covariance_factor_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) (t : Fin n → ℝ) :
    (∑ k, (∑ i, t i * supMeanCovarianceFactor μ X i k)^2) =
      ∑ i, ∑ j, t i * t j * (∫ ω, X i ω * X j ω ∂μ) := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (t i * t j) * ∑ k, supMeanCovarianceFactor μ X i k *
        supMeanCovarianceFactor μ X j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [supMean_covariance_factor_gram μ X hX]

end
end ASDExplicitGamma.Gaussian

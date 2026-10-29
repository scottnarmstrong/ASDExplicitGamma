module

public import ASDExplicitGamma.Gaussian.SupMeanFiniteLaw
public import ASDExplicitGamma.Gaussian.ConcentrationCountableRealizations

/-! The finite-realization premise of sharp concentration follows from joint Gaussianity. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- The canonical covariance square root realizes the complete finite observation
law on a standard Gaussian space. No independence among observations is required. -/
theorem supMean_gaussian_finite_realization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) :
    μ.map (fun ω i => X i ω) = (standardGaussianPi n).map
      (gaussianRealizationLinearVector (fun i k => supMeanCovarianceFactor μ X i k)) := by
  have hm : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_iff.mpr hX.1
  have hA : Measurable (gaussianRealizationLinearVector (fun i k => supMeanCovarianceFactor μ X i k)) := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun z : Fin n → ℝ => ∑ k, supMeanCovarianceFactor μ X i k * z k)
    fun_prop
  apply supMean_measure_eq_of_linear_laws
  intro t
  have ht : Measurable (fun x : Fin n → ℝ => ∑ i, t i * x i) := by fun_prop
  rw [AEMeasurable.map_map_of_aemeasurable ht.aemeasurable hm,
    Measure.map_map ht hA]
  change μ.map (fun ω => ∑ i, t i * X i ω) = _
  have hlaw : μ.map (fun ω => ∑ i, t i * X i ω) = gaussianReal 0
      (Real.toNNReal (∑ i, ∑ j, t i * t j * (∫ ω, X i ω * X j ω ∂μ))) := by
    simpa only [id_eq] using! hX.map_linearCombination_covariance id t
  rw [hlaw]
  have heq : (fun z => ∑ i, t i * gaussianRealizationLinearVector
      (fun i k => supMeanCovarianceFactor μ X i k) z i) =
      gaussianFiniteLinearForm (fun k => ∑ i, t i * supMeanCovarianceFactor μ X i k) := by
    funext z
    simp only [gaussianRealizationLinearVector, gaussianFiniteLinearForm, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ = (standardGaussianPi n).map (fun z => ∑ i, t i *
    gaussianRealizationLinearVector (fun i k => supMeanCovarianceFactor μ X i k) z i)
  rw [heq, supMean_standard_linear_law, supMean_covariance_factor_quadratic μ X hX]

/-- Sharp Borell concentration for an ordinary countable jointly Gaussian family.
Finite-dimensional realizations are proved internally from its Gaussian law. -/
theorem supMean_gaussian_countable_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hInt : Integrable (gaussianRealizationSup X) μ)
    (hFinite : ∀ᵐ ω ∂μ, BddAbove (Set.range fun k => X k ω))
    (hvar : ∀ k, Var[X k; μ] ≤ L^2) :
    μ.real {ω | t ≤ gaussianRealizationSup X ω - ∫ y, gaussianRealizationSup X y ∂μ} ≤
      Real.exp (-t^2 / (2*L^2)) := by
  apply measure_centered_tail_le_of_jointlyGaussianRealizations μ X hL ht hX.1 hInt hFinite hvar
  intro N
  exact ⟨fun i k => supMeanCovarianceFactor μ (fun i : Fin (N+1) => X i.val) i k,
    supMean_gaussian_finite_realization μ _ (hX.comp Fin.val)⟩

end
end ASDExplicitGamma.Gaussian

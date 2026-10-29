module

public import ASDExplicitGamma.Gaussian.SupMeanGaussianMoments

/-! Sharp centered MGF bounds for finite maxima under ordinary joint Gaussian laws. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- The actual finite maximum at a sample, with no replacement probability space. -/
def supMeanGaussianMaximum {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hn⟩, Finset.mem_univ _⟩ (fun i => X i ω)

/-- Row coefficient norms of the canonical factor are the actual variances. -/
theorem supMean_factor_row_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) (i : Fin n) :
    ‖(WithLp.toLp 2 (fun k => supMeanCovarianceFactor μ X i k) :
      EuclideanSpace ℝ (Fin n))‖^2 = Var[X i; μ] := by
  rw [EuclideanSpace.real_norm_sq_eq, supMean_gaussian_variance hX]
  simp_rw [pow_two]
  exact supMean_covariance_factor_gram μ X hX i i

/-- The sharp finite-maximum MGF follows from actual Gaussianity and a covariance
variance bound. A finite-realization hypothesis is not carried by the consumer. -/
theorem supMean_gaussian_maximum_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X)
    (L lam : ℝ) (hL : 0 ≤ L) (hvar : ∀ i, Var[X i; μ] ≤ L^2) :
    Integrable (supMeanGaussianMaximum hn X) μ ∧
    Integrable (fun ω => Real.exp (lam*supMeanGaussianMaximum hn X ω)) μ ∧
    Integrable (fun ω => Real.exp (lam*(supMeanGaussianMaximum hn X ω -
      ∫ y, supMeanGaussianMaximum hn X y ∂μ))) μ ∧
    (∫ ω, Real.exp (lam*(supMeanGaussianMaximum hn X ω -
      ∫ y, supMeanGaussianMaximum hn X y ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2) := by
  let A : Fin n → Fin n → ℝ := fun i k => supMeanCovarianceFactor μ X i k
  have hcoeff (i : Fin n) : ‖WithLp.toLp 2 (A i)‖ ≤ L := by
    apply (sq_le_sq₀ (norm_nonneg _) hL).mp
    exact (supMean_factor_row_norm_sq μ X hX i).trans_le (hvar i)
  have hb := integral_exp_centered_le_of_gaussianFiniteMaximum hn A (lam := lam) hcoeff
  let F : (Fin n → ℝ) → ℝ := fun z =>
    Finset.univ.sup' ⟨⟨0,hn⟩, Finset.mem_univ _⟩ (fun i => z i)
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ContinuousAt.finset_sup'_apply (s := Finset.univ)
      ⟨⟨0,hn⟩, Finset.mem_univ _⟩ (f := fun (i : Fin n) (z : Fin n → ℝ) => z i)
      (fun i _ => (continuous_apply i).continuousAt)
  have hF : Measurable F := hFc.measurable
  have hvec : IdentDistrib (fun ω i => X i ω) (gaussianRealizationLinearVector A)
      μ (standardGaussianPi n) := by
    refine ⟨aemeasurable_pi_iff.mpr hX.1, ?_, supMean_gaussian_finite_realization μ X hX⟩
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun z : Fin n → ℝ => ∑ k, A i k*z k)
    fun_prop
  have hmax : IdentDistrib (supMeanGaussianMaximum hn X) (gaussianFiniteMaximum hn A)
      μ (standardGaussianPi n) := hvec.comp hF
  have hmean := hmax.integral_eq
  have hexp := hmax.comp (show Measurable (fun z : ℝ => Real.exp (lam*z)) by fun_prop)
  have hcenter := hmax.comp (show Measurable (fun z : ℝ => Real.exp (lam*(z-
    ∫ y, supMeanGaussianMaximum hn X y ∂μ))) by fun_prop)
  rw [hmean] at hcenter
  rw [hmean]
  exact ⟨hmax.integrable_iff.mpr hb.1, hexp.integrable_iff.mpr hb.2.1,
    hcenter.integrable_iff.mpr hb.2.2.1, hcenter.integral_eq.trans_le hb.2.2.2⟩

end
end ASDExplicitGamma.Gaussian

module

public import ASDExplicitGamma.Gaussian.SupMeanKernelDifferenceMoment
public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor

/-! Finite projection variances and difference covariances of actual Gaussian kernel observations. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

/-- The actual variance of every finite projection is exactly its Hilbert
kernel combination norm. -/
theorem supMean_gaussian_kernel_combination_variance {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] (X : ι → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X) (K : ι → H)
    (hcov : ∀ i j, (∫ ω, X i ω*X j ω ∂μ) = ⟪K i,K j⟫) (a : ι → ℝ) :
    Var[(fun ω => ∑ i, a i*X i ω); μ] = ‖∑ i, a i • K i‖^2 := by
  rw [supMean_hilbert_combination_norm_sq]
  have hh := supMean_gaussian_combination_variance hX id a
  simpa only [id_eq, hcov] using! hh

/-- Differences of observations have the literal difference kernel covariance. -/
theorem supMean_gaussian_kernel_difference_covariance {Ω I H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (μ : Measure Ω)
    (X : I → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X) (K : I → H)
    (hcov : ∀ i j, (∫ ω, X i ω*X j ω ∂μ) = ⟪K i,K j⟫) (i j p q : I) :
    (∫ ω, (X i ω-X j ω)*(X p ω-X q ω) ∂μ) = ⟪K i-K j,K p-K q⟫ := by
  have hi (a b : I) : Integrable (fun ω => X a ω*X b ω) μ :=
    (hX.memLp a 2 (by simp)).integrable_mul (hX.memLp b 2 (by simp))
  have hs1 : Integrable (fun ω => X i ω*X p ω-X i ω*X q ω) μ := by
    simpa only [Pi.sub_apply] using! (hi i p).sub (hi i q)
  have hs2 : Integrable (fun ω => X i ω*X p ω-X i ω*X q ω-X j ω*X p ω) μ := by
    simpa only [Pi.sub_apply] using! hs1.sub (hi j p)
  have he : (fun ω => (X i ω-X j ω)*(X p ω-X q ω)) =
      (fun ω => X i ω*X p ω-X i ω*X q ω-X j ω*X p ω+X j ω*X q ω) := by
    funext ω
    ring
  rw [he, integral_add (f := fun ω => X i ω*X p ω-X i ω*X q ω-X j ω*X p ω)
      (g := fun ω => X j ω*X q ω) hs2 (hi j q),
    integral_sub (f := fun ω => X i ω*X p ω-X i ω*X q ω)
      (g := fun ω => X j ω*X p ω) hs1 (hi j p),
    integral_sub (f := fun ω => X i ω*X p ω) (g := fun ω => X i ω*X q ω) (hi i p) (hi i q),
    hcov, hcov, hcov, hcov, inner_sub_left, inner_sub_right, inner_sub_right]
  ring

end ASDExplicitGamma.Gaussian

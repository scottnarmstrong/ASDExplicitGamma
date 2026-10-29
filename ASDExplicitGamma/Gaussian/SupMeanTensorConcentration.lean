module

public import ASDExplicitGamma.Gaussian.SupMeanNormingSequence

/-! Sharp norm concentration of actual finite Gaussian tensors via fixed countable projections. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The finite tensor's Euclidean (Frobenius) norm. -/
def supMeanTensorNorm {Ω : Type*} {ι : Type} [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => X i ω) : EuclideanSpace ℝ ι)‖

/-- Fixed norming linear projections of that actual tensor. -/
def supMeanTensorProjection {Ω : Type*} {ι : Type} [Fintype ι]
    (X : ι → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, (supMeanNormingVector (EuclideanSpace ℝ ι) n) i * X i ω

/-- Coordinate projections are the usual Hilbert inner products. -/
theorem supMean_tensor_projection_inner {Ω : Type*} {ι : Type} [Fintype ι]
    (X : ι → Ω → ℝ) (n : ℕ) (ω : Ω) :
    supMeanTensorProjection X n ω =
      ⟪supMeanNormingVector (EuclideanSpace ℝ ι) n, WithLp.toLp 2 (fun i => X i ω)⟫ := by
  simp only [supMeanTensorProjection, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, mul_comm]

/-- This countable supremum is exactly the finite tensor norm at every sample. -/
theorem supMean_tensor_projection_sup {Ω : Type*} [MeasurableSpace Ω] {ι : Type} [Fintype ι]
    (X : ι → Ω → ℝ) : gaussianRealizationSup (supMeanTensorProjection X) = supMeanTensorNorm X := by
  funext ω
  simp only [gaussianRealizationSup, supMean_tensor_projection_inner, supMeanTensorNorm]
  exact (supMean_norm_eq_countable_inner _ _).symm

/-- A tensor covariance operator bound gives the sharp centered norm MGF. All
norm integrability, countable boundedness and finite Gaussian realizations are derived. -/
theorem supMean_gaussian_tensor_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X) (L lam : ℝ) (hL : 0 ≤ L)
    (hvar : ∀ a : ι → ℝ, Var[(fun ω => ∑ i, a i*X i ω); μ] ≤ L^2*(∑ i, a i^2)) :
    Integrable (fun ω => Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ y, supMeanTensorNorm X y ∂μ))) μ ∧
    (∫ ω, Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ y, supMeanTensorNorm X y ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2) := by
  let E := EuclideanSpace ℝ ι
  have hg : IsCenteredGaussianFamily μ (supMeanTensorProjection X) :=
    hX.finite_linear_image (fun (_ : ℕ) i => i)
      (fun n i => (supMeanNormingVector E n) i)
  have hi : Integrable (supMeanTensorNorm X) μ :=
    (supMean_gaussian_tensor_moment μ X hX).1.integrable (by norm_num)
  have hb : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => supMeanTensorProjection X n ω) := by
    apply Filter.Eventually.of_forall
    intro ω
    refine ⟨supMeanTensorNorm X ω, ?_⟩
    rintro z ⟨n,rfl⟩
    change supMeanTensorProjection X n ω ≤ supMeanTensorNorm X ω
    rw [supMean_tensor_projection_inner]
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (supMean_norming_vector_norm_le E n) (norm_nonneg _)).trans_eq (one_mul _))
  have hv (n : ℕ) : Var[supMeanTensorProjection X n; μ] ≤ L^2 := by
    have hn := supMean_norming_vector_norm_le E n
    have hs : (∑ i, (supMeanNormingVector E n) i^2) ≤ 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact pow_le_one₀ (norm_nonneg _) hn
    exact (hvar (fun i => (supMeanNormingVector E n) i)).trans
      ((mul_le_mul_of_nonneg_left hs (sq_nonneg L)).trans_eq (mul_one _))
  have hh := supMean_gaussian_countable_mgf μ (supMeanTensorProjection X) hg L lam hL hv
    (by simpa only [supMean_tensor_projection_sup] using hi) hb
  simpa only [supMean_tensor_projection_sup] using hh

end
end ASDExplicitGamma.Gaussian

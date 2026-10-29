module

public import ASDExplicitGamma.Gaussian.HilbertKernel
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Orthogonal scalar-L2 embeddings into the actual white Hilbert space.
These reconstruct covariance kernels from complete square-summable mode data. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- Embed a scalar spatial L2 field along one actual orthonormal white
basis vector. This is a genuine isometry, not a bound assumed from its use. -/
def oldSignedBasisLpEmbedding {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (i : I) :
    Lp ℝ 2 mu →ₗᵢ[ℝ] Lp E 2 mu where
  toLinearMap := (((LinearIsometry.toSpanSingleton ℝ E (e.orthonormal.norm_eq_one i)).toContinuousLinearMap).compLpL 2 mu).toLinearMap
  norm_map' f := by
    let L := LinearIsometry.toSpanSingleton ℝ E (e.orthonormal.norm_eq_one i)
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [ASDExplicitGamma.Gaussian.l2_norm_sq,ASDExplicitGamma.Gaussian.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [L.toContinuousLinearMap.coeFn_compLpL f] with x hx
    change ‖(L.toContinuousLinearMap.compLpL 2 mu f) x‖ ^ 2 = ‖f x‖ ^ 2
    rw [hx]
    exact congrArg (fun t : ℝ => t^2) (L.norm_map (f x))

/-- The basis embedding has its literal pointwise scalar-times-vector
representative. -/
theorem old_signed_basis_lp_embedding_coeFn {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (i : I) (f : Lp ℝ 2 mu) :
    oldSignedBasisLpEmbedding mu e i f =ᵐ[mu] fun x => f x • e i := by
  exact (LinearIsometry.toSpanSingleton ℝ E (e.orthonormal.norm_eq_one i)).toContinuousLinearMap.coeFn_compLpL f

/-- Different actual white basis vectors give orthogonal copies of the
full scalar spatial L2 space. -/
theorem old_signed_basis_lp_orthogonalFamily {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) :
    OrthogonalFamily ℝ (fun _ : I => Lp ℝ 2 mu) (oldSignedBasisLpEmbedding mu e) := by
  intro i j hij f g
  rw [L2.inner_def]
  have he := e.orthonormal.inner_eq_zero hij
  have hi : (∫ x,inner ℝ ((oldSignedBasisLpEmbedding mu e i f) x)
      ((oldSignedBasisLpEmbedding mu e j g) x) ∂mu)=∫ _ : X,(0:ℝ) ∂mu := by
    apply integral_congr_ae
    filter_upwards [old_signed_basis_lp_embedding_coeFn mu e i f,
      old_signed_basis_lp_embedding_coeFn mu e j g] with x hx hy
    rw [hx,hy,real_inner_smul_left,real_inner_smul_right,he,mul_zero,mul_zero]
  rw [hi,integral_zero]

/-- Actual square-summable scalar L2 mode data reconstruct a convergent
white-Hilbert spatial L2 kernel. No absolute sum of mode norms is required. -/
theorem old_signed_basis_lp_summable {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (f : I → Lp ℝ 2 mu)
    (hf : Summable (fun i => ‖f i‖^2)) :
    Summable (fun i => oldSignedBasisLpEmbedding mu e i (f i)) :=
  ((old_signed_basis_lp_orthogonalFamily mu e).summable_iff_norm_sq_summable f).mpr hf

end
end ASDExplicitGamma.Native

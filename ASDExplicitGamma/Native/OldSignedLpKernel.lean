module

public import ASDExplicitGamma.Native.OldSignedBasisLpEmbedding

/-! Exact coefficient recovery and energy of reconstructed spatial
white-Hilbert kernels. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory ASDExplicitGamma.Gaussian
noncomputable section

/-- The complete orthogonal mode sum as a genuine spatial Hilbert L2 field. -/
def oldSignedLpKernel {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (f : I → Lp ℝ 2 mu) : Lp E 2 mu :=
  ∑' i,oldSignedBasisLpEmbedding mu e i (f i)

/-- Testing one embedded mode with a white basis vector recovers exactly
its scalar coefficient, and vanishes for all other modes. -/
theorem old_signed_basis_lp_coefficient {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DecidableEq I] (mu : Measure X) (e : HilbertBasis I ℝ E) (i j : I) (f : Lp ℝ 2 mu) :
    (innerSL ℝ (e i)).compLpL 2 mu (oldSignedBasisLpEmbedding mu e j f)=
      if i=j then f else 0 := by
  classical
  apply Lp.ext
  filter_upwards [(innerSL ℝ (e i)).coeFn_compLpL (oldSignedBasisLpEmbedding mu e j f),
    old_signed_basis_lp_embedding_coeFn mu e j f,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu)] with x hx hy hz
  rw [hx,hy]
  simp only [innerSL_apply_apply,real_inner_smul_right,orthonormal_iff_ite.mp e.orthonormal]
  split_ifs
  · simp
  · simpa only [Pi.zero_apply,mul_zero] using hz.symm

/-- The full sum has the literal scalar modes as its actual white
coefficients. Square summability is the only convergence input. -/
theorem old_signed_lp_kernel_coefficient {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (f : I → Lp ℝ 2 mu)
    (hf : Summable (fun i => ‖f i‖^2)) (i : I) :
    (innerSL ℝ (e i)).compLpL 2 mu (oldSignedLpKernel mu e f)=f i := by
  classical
  rw [oldSignedLpKernel,((innerSL ℝ (e i)).compLpL 2 mu).map_tsum
    (old_signed_basis_lp_summable mu e f hf)]
  simp_rw [old_signed_basis_lp_coefficient]
  simp

/-- Exact complete mode energy, with the ordinary spatial L2 measure. -/
theorem old_signed_lp_kernel_norm_sq {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (f : I → Lp ℝ 2 mu)
    (hf : Summable (fun i => ‖f i‖^2)) :
    ‖oldSignedLpKernel mu e f‖^2=∑' i,‖f i‖^2 := by
  rw [←hilbertKernel_basis_tsum_eq mu (oldSignedLpKernel mu e f) e]
  congr 1
  funext i
  rw [hilbertKernel]
  change ‖(innerSL ℝ (e i)).compLpL 2 mu (oldSignedLpKernel mu e f)‖^2=‖f i‖^2
  rw [old_signed_lp_kernel_coefficient mu e f hf]

end
end ASDExplicitGamma.Native

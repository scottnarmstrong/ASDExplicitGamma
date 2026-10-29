module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovariancePairing
public import ASDExplicitGamma.Native.OldSignedH1KernelEnergy
public import ASDExplicitGamma.Native.OldSignedWhiteRow
public import ASDExplicitGamma.Triadic.HilbertCubePoincare
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry

/-! Actual white-Hilbert realization of the finite-parent minus field.
Frozen covariance is the inner product of its genuine cell mean and the
physical coefficient-section mean, not an assigned covariance matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- The complete finite-parent minus kernel in each load/output coordinate. -/
def oldHessianMinusKernel (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (i k : Fin 2) : HilbertH1Function (openCubeSet Q) WhiteNoise :=
  oldSignedNormalizedH1Kernel Q whiteBasis (fun j => mainFlatMinusCoordinate Q b L j (i,k))
    (old_signed_flat_minus_value_series Q b L (i,k))
    (old_signed_flat_minus_gradient_series Q b L (i,k))

/-- Every actual white coordinate agrees with the original finite-parent
flat field on every fine cell, in the normalized source measure. -/
theorem old_hessian_minus_kernel_coefficient (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis j) ((oldHessianMinusKernel Q b L i k).toFun x)) =ᵐ[
      normalizedCubeMeasure U] fun x => (oldSignedFlatMinusBlock Q b L j i x).1 k := by
  have hc := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => mainFlatMinusCoordinate Q b L j (i,k))
    (old_signed_flat_minus_value_series Q b L (i,k))
    (old_signed_flat_minus_gradient_series Q b L (i,k)) j
  have hu := ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hU) hc
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hu

/-- Coordinate means of the same genuine kernel are exactly the means
used in the frozen matrix; no mean or projection representative is changed. -/
theorem old_hessian_minus_kernel_mean (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    inner ℝ (whiteBasis j) (hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)=
      (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k := by
  let u := (oldHessianMinusKernel Q b L i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hm : MemLp (oldHessianMinusKernel Q b L i k).toFun 2 (normalizedCubeMeasure U) :=
    u.memL2_normalized U
  rw [←hilbertCubeAverage_inner U (whiteBasis j) hm]
  change cubeAverage U _=cubeAverage U _
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_congr_ae (old_hessian_minus_kernel_coefficient Q depth b L U hU i k j)

/-- The physical coefficient section is square integrable on every cell. -/
theorem old_hessian_white_section_memLp (U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    MemLp (q3Section b L h3Zero) 2 (normalizedCubeMeasure U) :=
  (main_continuous_memLp_top U (old_signed_white_section_contDiff b L).continuous).mono_exponent (by simp)

/-- Exact mean representation of each actual physical coefficient mode. -/
theorem old_hessian_white_section_mean (U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (j : whiteBasisIndex) :
    cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))=
      inner ℝ (whiteBasis j) (hilbertCubeAverage U (q3Section b L h3Zero)) :=
  hilbertCubeAverage_inner U (whiteBasis j) (old_hessian_white_section_memLp U b L)

/-- The actual frozen matrix is the Hilbert inner product of the genuine
coefficient and finite-parent minus cell means. This identity uses the full
white family and its already established convergent covariance series. -/
theorem old_hessian_mean_covariance_kernel (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    oldHessianMeanCovariance Q U b L k i=
      inner ℝ (hilbertCubeAverage U (q3Section b L h3Zero))
        (hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun) := by
  have hs := whiteBasis.hasSum_inner_mul_inner
    (hilbertCubeAverage U (q3Section b L h3Zero))
    (hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)
  have hs' : HasSum (fun j : whiteBasisIndex =>
      cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))*
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k)
      (inner ℝ (hilbertCubeAverage U (q3Section b L h3Zero))
        (hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)) := by
    apply hs.congr_fun
    intro j
    rw [real_inner_comm (whiteBasis j),
      old_hessian_minus_kernel_mean Q depth b L U hU i k j,
      ←old_hessian_white_section_mean U b L j]
  exact (old_hessian_mean_covariance_entry Q depth b L U hU i k).1.hasSum.unique hs'

end
end ASDExplicitGamma.Scalar

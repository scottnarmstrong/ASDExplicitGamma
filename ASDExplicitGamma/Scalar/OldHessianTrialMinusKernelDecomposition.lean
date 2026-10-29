module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCentering
public import ASDExplicitGamma.Native.OldSignedFlatModeDecomposition
public import ASDExplicitGamma.Native.OldSignedRemainderCovariance

/-! Exact finite-parent minus kernel decomposition on every fine cell.
The harmonic boundary kernel and the mean-free covariance both remain. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Whole-plane projected kernel with the original input quarter turn. -/
def oldHessianProjectedMinusKernel (b : ℝ) (L : {l : ℝ // 0<l})
    (x : Vec 2) (i k : Fin 2) : WhiteNoise :=
  ∑ c : Fin 2,responsePlanarJ c i • oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) k c

theorem old_hessian_projected_minus_kernel_coefficient (b : ℝ) (L : {l : ℝ // 0<l})
    (x : Vec 2) (i k : Fin 2) (w : WhiteNoise) :
    inner ℝ w (oldHessianProjectedMinusKernel b L x i k)=oldSignedRotatedProjectedField b L w i x k := by
  simp only [oldHessianProjectedMinusKernel,Fin.sum_univ_two,inner_add_right,real_inner_smul_right,
    oldSignedRotatedProjectedField,oldSignedPhysicalProjectedField,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

/-- The projected same-point covariance is exactly the one-half physical
variance times J, with its input orientation unchanged. -/
theorem old_hessian_projected_minus_point_covariance (b : ℝ) (L : {l : ℝ // 0<l})
    (x : Vec 2) (i k : Fin 2) :
    inner ℝ (q3Section b L h3Zero x) (oldHessianProjectedMinusKernel b L x i k)=
      (b^2/2)*responsePlanarJ k i := by
  have hx : L.1 • (L.1⁻¹ • x)=x := by rw [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul]
  have hc (j l : Fin 2) := old_signed_projected_white_point_covariance b L (L.1⁻¹ • x) j l
  rw [hx] at hc
  simp only [oldHessianProjectedMinusKernel,inner_sum,real_inner_smul_right,hc]
  fin_cases i <;> fin_cases k <;> norm_num [responsePlanarJ,Fin.sum_univ_two] <;> ring

/-- The actual parent harmonic kernel has the original remainder modes on
every fine cell, with no harmonic extension chosen on the child. -/
theorem old_hessian_remainder_kernel_coefficient (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis j) ((oldSignedRemainderKernel Q b L false (i,k)).toFun x)) =ᵐ[
      normalizedCubeMeasure U] oldSignedRemainderCoordinate Q b L false j (i,k) := by
  have hc := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => oldSignedRemainderCoordinate Q b L false j (i,k))
    (old_signed_coordinate_value_summable Q _ (old_signed_remainder_coordinate_value_trace Q b L false).summable (i,k))
    (old_signed_coordinate_derivative_summable Q _ (old_signed_remainder_coordinate_gradient_bound Q b L false).1 (i,k)) j
  have hu := ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hU) hc
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hu

/-- The complete finite-parent minus kernel is the whole-plane projected
kernel plus its actual parent harmonic correction, on the same fine cell. -/
theorem old_hessian_minus_kernel_decomposition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    (oldHessianMinusKernel Q b L i k).toFun =ᵐ[normalizedCubeMeasure U]
      fun x => oldHessianProjectedMinusKernel b L x i k+
        (oldSignedRemainderKernel Q b L false (i,k)).toFun x := by
  have hc : ∀ᵐ x ∂normalizedCubeMeasure U,∀ j : whiteBasisIndex,
      inner ℝ (whiteBasis j) ((oldHessianMinusKernel Q b L i k).toFun x)=
        inner ℝ (whiteBasis j) (oldHessianProjectedMinusKernel b L x i k+
          (oldSignedRemainderKernel Q b L false (i,k)).toFun x) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [old_hessian_minus_kernel_coefficient Q depth b L U hU i k j,
      old_hessian_remainder_kernel_coefficient Q depth b L U hU i k j] with x hx hy
    rw [hx,inner_add_right,old_hessian_projected_minus_kernel_coefficient,hy]
    exact old_signed_flat_coordinate_decomposition Q b L false j i k x
  filter_upwards [hc] with x hx
  apply whiteBasis.repr.injective
  ext j
  simpa only [HilbertBasis.repr_apply_apply] using hx j

/-- The literal full point covariance is its exact bulk plus the actual
harmonic boundary covariance. The latter is not removed by centering. -/
theorem old_hessian_minus_point_covariance (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    (fun x => inner ℝ (q3Section b L h3Zero x) ((oldHessianMinusKernel Q b L i k).toFun x)) =ᵐ[
      normalizedCubeMeasure U]
      fun x => (b^2/2)*responsePlanarJ k i+
        inner ℝ (q3Section b L h3Zero x) ((oldSignedRemainderKernel Q b L false (i,k)).toFun x) := by
  filter_upwards [old_hessian_minus_kernel_decomposition Q depth b L U hU i k] with x hx
  rw [hx,inner_add_right,old_hessian_projected_minus_point_covariance]

end
end ASDExplicitGamma.Scalar

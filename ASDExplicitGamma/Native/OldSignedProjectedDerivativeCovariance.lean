module

public import ASDExplicitGamma.Native.OldSignedProjectedDerivativeEnergy
public import ASDExplicitGamma.Native.OldSignedPlanarProjection

/-! The rank-one Helmholtz covariance identity for the actual differentiated
physical kernels. This recovers the sharp derivative trace without a loss. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- The differentiated projected kernels retain the matrix symmetry. -/
theorem old_signed_projected_derivative_white_symmetric (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j k : Fin 2) :
    oldSignedProjectedDerivativeWhiteKernel b L x i j k=oldSignedProjectedDerivativeWhiteKernel b L x j i k := by
  have hF := old_signed_projected_white_hasFDerivAt b L x i j
  have hG := old_signed_projected_white_hasFDerivAt b L x j i
  have he : (fun y => oldSignedProjectedWhiteKernel b L y i j)=
      (fun y => oldSignedProjectedWhiteKernel b L y j i) :=
    funext (fun y => old_signed_projected_white_kernel_symmetric b L y i j)
  rw [he] at hF
  have hh := congrArg (fun D : Vec 2 →L[ℝ] WhiteNoise => D (basisVec k)) (hF.unique hG)
  simpa only [old_signed_projected_white_derivative_basis] using hh

/-- At every frequency the differentiated rank-one matrix has its exact
determinant-zero pairing identity, including at zero frequency. -/
theorem old_signed_projected_derivative_point_pairing (x : Vec 2) (k : Fin 2) (xi : Q3FrequencyPlane) :
    inner ℂ (oldSignedProjectedDerivativeValue x 0 0 k xi) (oldSignedProjectedDerivativeValue x 1 1 k xi)=
      inner ℂ (oldSignedProjectedDerivativeValue x 0 1 k xi) (oldSignedProjectedDerivativeValue x 0 1 k xi) := by
  simp only [oldSignedProjectedDerivativeValue,oldSignedProjectedCharacterValue,RCLike.inner_apply,
    map_mul,Complex.conj_ofReal]
  norm_num [oldSignedHelmholtzEntry,oldSignedFrequency]
  ring

/-- The same exact pairing holds in the actual real physical derivative
kernels, by the full isometry and spectral reality. -/
theorem old_signed_projected_derivative_white_pairing (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (k : Fin 2) :
    inner ℝ (oldSignedProjectedDerivativeWhiteKernel b L x 0 0 k)
      (oldSignedProjectedDerivativeWhiteKernel b L x 1 1 k)=
      ‖oldSignedProjectedDerivativeWhiteKernel b L x 0 1 k‖^2 := by
  rw [←real_inner_self_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [←old_signed_white_complexify_inner,←old_signed_white_complexify_inner]
  simp only [oldSignedProjectedDerivativeWhiteKernel,
    old_signed_potential_white_map_complexify b L _ (old_signed_projected_derivative_real b x 0 0 k),
    old_signed_potential_white_map_complexify b L _ (old_signed_projected_derivative_real b x 1 1 k),
    old_signed_potential_white_map_complexify b L _ (old_signed_projected_derivative_real b x 0 1 k),
    LinearIsometry.inner_map_map]
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [old_signed_projected_derivative_coeFn b x 0 0 k,
    old_signed_projected_derivative_coeFn b x 1 1 k,old_signed_projected_derivative_coeFn b x 0 1 k]
      with xi h00 h11 h01
  rw [h00,h11,h01]
  exact old_signed_projected_derivative_point_pairing x k xi

/-- Sharp full-matrix derivative energy for each dimensionless derivative
direction. The actual scalar covariance moment is recovered by differentiation. -/
theorem old_signed_projected_derivative_white_total_energy (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (k : Fin 2) :
    (∑ i : Fin 2,∑ j : Fin 2,‖oldSignedProjectedDerivativeWhiteKernel b L x i j k‖^2)=b^2*(78/5:ℝ) := by
  have ht := old_signed_white_trace_derivative_energy b L x k
  rw [norm_add_sq_real,old_signed_projected_derivative_white_pairing] at ht
  simp only [Fin.sum_univ_two]
  rw [old_signed_projected_derivative_white_symmetric b L x 1 0 k]
  linarith only [ht]

end
end ASDExplicitGamma.Native

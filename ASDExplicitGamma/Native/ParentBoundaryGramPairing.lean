module

public import ASDExplicitGamma.Native.ParentBoundaryGram
public import ASDExplicitGamma.Native.ParentBoundaryCentering

/-! Physical source testing of the genuine projected Gram fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- Exact source-testing identity of the actual orthogonal projection. -/
theorem parent_boundary_projected_source_pairing (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v u : Vec 2) (w : WhiteNoise) :
    inner ℝ (parentBoundaryDirichletLoadOperator Q b L v w)
      (parentBoundaryDirichletLoadOperator Q b L u w) =
    inner ℝ (parentBoundaryRawLoadOperator Q b L v w)
      (parentBoundaryDirichletLoadOperator Q b L u w) := by
  let p := (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule
  have hh := p.starProjection_inner_eq_zero (parentBoundaryRawLoadOperator Q b L v w)
    (p.starProjection (parentBoundaryRawLoadOperator Q b L u w))
    (p.starProjection_apply_mem _)
  rw [inner_sub_left] at hh
  exact (sub_eq_zero.mp hh).symm

/-- Testing one projected load against a physical scalar convolution
coordinate gives its literal mixed Gram coefficient. -/
theorem parent_boundary_gram_coordinate_integral (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : Vec 2) (n : whiteBasisIndex) (k : Fin 2) :
    (∫ x,q3Convolution b L h3Zero (whiteBasis n) x *
      (lambda8Q3GaussianModeParentPotential Q b L u n).toH1Function.grad x k
        ∂normalizedCubeMeasure Q) =
    (cubeVolume Q)⁻¹ * inner ℝ
      (parentBoundaryDirichletLoadOperator Q b L (basisVec k) (whiteBasis n))
      (parentBoundaryDirichletLoadOperator Q b L u (whiteBasis n)) := by
  rw [parent_boundary_projected_source_pairing,parent_boundary_dirichlet_load_basis,
    integral_normalized_eq_open,L2.inner_def]
  apply congrArg (fun z : ℝ => (cubeVolume Q)⁻¹*z)
  apply integral_congr_ae
  filter_upwards [parent_boundary_raw_load_operator_coeFn Q b L (basisVec k) (whiteBasis n),
    (lambda8Q3GaussianModeParentPotential Q b L u n).toH1Function.coeFn_gradToHilbertVectorL2]
    with x hr hp
  rw [hr,hp]
  simp only [hilbertifyVecField,HilbertVec.inner_def,HilbertVec.toVec_ofVec,vecDot_smul_left,vecDot_basisVec_left]

end
end ASDExplicitGamma.Native

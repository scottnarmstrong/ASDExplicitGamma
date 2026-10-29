module

public import ASDExplicitGamma.Native.ParentBoundaryLoadTrace
public import ASDExplicitGamma.Native.ParentBoundaryWhiteBasis

/-! Physical square symmetry of the complete parent Dirichlet trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Reflection intertwines the actual raw vector load operators, with
both the observation point and complete white realization transformed. -/
theorem parent_boundary_raw_load_flip (m : ℤ) (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryVectorFlip m i (parentBoundaryRawLoadOperator (originCube 2 m) b L v w) =
      parentBoundaryRawLoadOperator (originCube 2 m) b L
        (signFlipVecContinuousLinearEquiv i v) (parentBoundaryWhiteFlip i w) := by
  apply Lp.ext
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i m
  filter_upwards [parent_boundary_vector_flip_coeFn m i
      (parentBoundaryRawLoadOperator (originCube 2 m) b L v w),
    hmp.quasiMeasurePreserving.ae_eq_comp
      (parent_boundary_raw_load_operator_coeFn (originCube 2 m) b L v w),
    parent_boundary_raw_load_operator_coeFn (originCube 2 m) b L
      (signFlipVecContinuousLinearEquiv i v) (parentBoundaryWhiteFlip i w)] with x ht hv hr
  simp only [Function.comp_apply] at hv
  rw [ht,hv,hr,parent_boundary_convolution_flip]
  simp only [HilbertVec.toVec_ofVec,map_smul]

/-- Coordinate swap intertwines those same physical source operators. -/
theorem parent_boundary_raw_load_swap (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryVectorSwap m (parentBoundaryRawLoadOperator (originCube 2 m) b L v w) =
      parentBoundaryRawLoadOperator (originCube 2 m) b L
        (swapVecContinuousLinearEquiv (0 : Fin 2) 1 v) (parentBoundaryWhiteSwap w) := by
  apply Lp.ext
  have hmp := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube (0 : Fin 2) 1 m
  filter_upwards [parent_boundary_vector_swap_coeFn m
      (parentBoundaryRawLoadOperator (originCube 2 m) b L v w),
    hmp.quasiMeasurePreserving.ae_eq_comp
      (parent_boundary_raw_load_operator_coeFn (originCube 2 m) b L v w),
    parent_boundary_raw_load_operator_coeFn (originCube 2 m) b L
      (swapVecContinuousLinearEquiv (0 : Fin 2) 1 v) (parentBoundaryWhiteSwap w)] with x ht hv hr
  simp only [Function.comp_apply] at hv
  rw [ht,hv,hr,parent_boundary_convolution_swap]
  simp only [HilbertVec.toVec_ofVec,map_smul]

/-- The genuine parent Dirichlet load has the same reflection law. -/
theorem parent_boundary_dirichlet_load_flip (m : ℤ) (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryVectorFlip m i (parentBoundaryDirichletLoadOperator (originCube 2 m) b L v w) =
      parentBoundaryDirichletLoadOperator (originCube 2 m) b L
        (signFlipVecContinuousLinearEquiv i v) (parentBoundaryWhiteFlip i w) := by
  change parentBoundaryVectorFlip m i (lambda8DirichletProjection _
    (parentBoundaryRawLoadOperator (originCube 2 m) b L v w)) =
      lambda8DirichletProjection _ _
  rw [parent_boundary_dirichlet_projection_flip,parent_boundary_raw_load_flip]
  rfl

/-- The genuine parent Dirichlet load has the same coordinate swap law. -/
theorem parent_boundary_dirichlet_load_swap (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryVectorSwap m (parentBoundaryDirichletLoadOperator (originCube 2 m) b L v w) =
      parentBoundaryDirichletLoadOperator (originCube 2 m) b L
        (swapVecContinuousLinearEquiv (0 : Fin 2) 1 v) (parentBoundaryWhiteSwap w) := by
  change parentBoundaryVectorSwap m (lambda8DirichletProjection _
    (parentBoundaryRawLoadOperator (originCube 2 m) b L v w)) =
      lambda8DirichletProjection _ _
  rw [parent_boundary_dirichlet_projection_swap,parent_boundary_raw_load_swap]
  rfl

/-- The complete physical Dirichlet square trace is invariant under
reflection of the load vector. All mode convergence is proved internally. -/
theorem parent_boundary_dirichlet_trace_flip (m : ℤ) (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) :
    (∑' n, ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
      (signFlipVecContinuousLinearEquiv i v) (whiteBasis n)‖^2) =
    ∑' n, ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L v (whiteBasis n)‖^2 := by
  let e := HilbertBasis.ofRepr ((parentBoundaryWhiteFlipEquiv i).symm.trans whiteBasis.repr)
  rw [parent_boundary_dirichlet_load_trace_basis whiteBasis e]
  apply tsum_congr
  intro n
  change ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
    (signFlipVecContinuousLinearEquiv i v) (parentBoundaryWhiteFlip i (whiteBasis n))‖^2 = _
  rw [←parent_boundary_dirichlet_load_flip,LinearIsometry.norm_map]

/-- The complete physical Dirichlet square trace is invariant under swap. -/
theorem parent_boundary_dirichlet_trace_swap (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) :
    (∑' n, ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
      (swapVecContinuousLinearEquiv (0 : Fin 2) 1 v) (whiteBasis n)‖^2) =
    ∑' n, ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L v (whiteBasis n)‖^2 := by
  let e := HilbertBasis.ofRepr (parentBoundaryWhiteSwapEquiv.symm.trans whiteBasis.repr)
  rw [parent_boundary_dirichlet_load_trace_basis whiteBasis e]
  apply tsum_congr
  intro n
  change ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
    (swapVecContinuousLinearEquiv (0 : Fin 2) 1 v) (parentBoundaryWhiteSwap (whiteBasis n))‖^2 = _
  rw [←parent_boundary_dirichlet_load_swap,LinearIsometry.norm_map]

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.ParentBoundaryLoadSymmetry
public import ASDExplicitGamma.Native.ParentBoundaryLoadAlgebra

/-! Scalar Gram form of the actual parent Dirichlet projection. Symmetry
is proved for complete physical covariance before any quantitative bound. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Actual complete normalized two-load Dirichlet Gram matrix. -/
def parentBoundaryDirichletGram (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i j : Fin 2) : ℝ :=
  (cubeVolume Q)⁻¹ * ∑' n : whiteBasisIndex,
    inner ℝ (parentBoundaryDirichletLoadOperator Q b L (basisVec i) (whiteBasis n))
      (parentBoundaryDirichletLoadOperator Q b L (basisVec j) (whiteBasis n))

/-- The complete Gram matrix is symmetric, before any spatial symmetry. -/
theorem parent_boundary_dirichlet_gram_symm (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i j : Fin 2) :
    parentBoundaryDirichletGram Q b L i j=parentBoundaryDirichletGram Q b L j i := by
  unfold parentBoundaryDirichletGram
  apply congrArg (fun z : ℝ => (cubeVolume Q)⁻¹*z)
  exact tsum_congr (fun _ => real_inner_comm _ _)

/-- Equal diagonal entries follow from the actual square swap, applied to
the complete trace rather than to finite basis truncations. -/
theorem parent_boundary_dirichlet_gram_diagonal (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletGram (originCube 2 m) b L 0 0=
      parentBoundaryDirichletGram (originCube 2 m) b L 1 1 := by
  have hs := parent_boundary_dirichlet_trace_swap m b L (basisVec 0)
  simp only [swapVecContinuousLinearEquiv_basisVec,Equiv.swap_apply_left] at hs
  unfold parentBoundaryDirichletGram
  simp only [real_inner_self_eq_norm_sq]
  exact congrArg (fun z : ℝ => (cubeVolume (originCube 2 m))⁻¹*z) hs.symm

/-- Physical scalar multiples include the sign of the second Gram load. -/
theorem parent_boundary_dirichlet_load_neg (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryDirichletLoadOperator Q b L (-v) w =
      -parentBoundaryDirichletLoadOperator Q b L v w := by
  simpa only [neg_one_smul] using parent_boundary_dirichlet_load_smul Q b L (-1) v w

/-- The off-diagonal entry vanishes by reflection and exact complete
quadratic expansions. All mixed sums have proved absolute convergence. -/
theorem parent_boundary_dirichlet_gram_offdiagonal (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletGram (originCube 2 m) b L 0 1=0 := by
  have hs := parent_boundary_dirichlet_trace_flip m 1 b L (basisVec 0+basisVec 1)
  have hv : signFlipVecContinuousLinearEquiv (1 : Fin 2) (basisVec 0+basisVec 1)=
      basisVec 0+(-basisVec 1) := by
    ext k
    fin_cases k <;> norm_num [signFlipVecContinuousLinearEquiv_apply,
      matVecMul_signFlipMatrix_apply,basisVec,Pi.single_apply]
  rw [hv,parent_boundary_dirichlet_trace_add,parent_boundary_dirichlet_trace_add] at hs
  simp_rw [parent_boundary_dirichlet_load_neg,norm_neg,inner_neg_right,tsum_neg] at hs
  have hz : (∑' n : whiteBasisIndex,inner ℝ
      (parentBoundaryDirichletLoadOperator (originCube 2 m) b L (basisVec 0) (whiteBasis n))
      (parentBoundaryDirichletLoadOperator (originCube 2 m) b L (basisVec 1) (whiteBasis n)))=0 := by
    linarith only [hs]
  simp only [parentBoundaryDirichletGram,hz,mul_zero]

end
end ASDExplicitGamma.Native

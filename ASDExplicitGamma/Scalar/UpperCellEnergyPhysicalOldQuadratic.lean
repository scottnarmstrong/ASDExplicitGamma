module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalOldBook

/-! Pointwise positivity and the trace-majorant cap for the physical OLD
quadratic in the fixed true scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Algsuperdiff.Section3
noncomputable section

/-- The physical OLD coarse matrix is the normalized cutoff matrix. -/
theorem upper_cell_physical_old_coarse_matrix
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (oldCutoffSkewCoefficient n Q ω)) =
    coarseBlockMatrix (cubeSet Q)
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  rw [cube_coarseMatrix_eq_open]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact upper_cell_reset_frame_coefficient M n n Q ω hx

/-- The actual OLD quadratic is nonnegative and bounded by the same trace
majorant as the initial inverse lambda, for every sample and loading. -/
theorem upper_cell_physical_old_quadratic_bounds
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2) (P : BlockVec 2) :
    let Q := originCube 2 (n-ell)
    let E := blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (oldCutoffSkewCoefficient n Q ω))) P)
    0≤E ∧ E≤(1+2*(lagTraceHistory M n ell ω).toReal+
      Real.sqrt (2*(lagTraceHistory M n ell ω).toReal))*blockVecDot P P := by
  dsimp only
  let Q := originCube 2 (n-ell)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let k := sigma⁻¹ • oldCutoffSkewCoefficient n Q ω
  constructor
  · have hh := sensitivityCoarseMatrixPathQuadratic_nonneg (M.nu/sigma)
      (div_pos M.nu_pos (Annealed.sigmaBar M n).property) k 0 P 0
    simp only [sensitivityCoarseMatrixPathQuadratic,sensitivityResponseCoefficientPath,
      zero_smul,add_zero] at hh
    rw [upper_cell_normalized_book_matrix Q M.nu sigma M.nu_pos
      (Annealed.sigmaBar M n).property] at hh
    exact hh
  · rw [upper_cell_physical_old_coarse_matrix]
    have hmem : Q ∈ descendantsAtDepth Q 0 := by simp [descendantsAtDepth_zero]
    have hn := upper_cell_old_descendant_norm_bound M n ell ω 0 Q hmem
    simp only [pow_zero,one_mul] at hn
    exact (block_quadratic_le_operator_norm _ P).trans
      (mul_le_mul_of_nonneg_right hn (blockVecDot_nonneg P))

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBookSubadditivity
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldDepthBound

/-! The OLD Book matrices in the descendant comparison are precisely the
physical normalized cutoff matrices controlled by the accepted history. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual initial sensitivity family agrees with the normalized OLD
coefficient on every descendant of the observation cube. -/
theorem upper_cell_physical_old_book_matrix
    (M : ABKModel 2) (n : ℤ) (Q R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) (ω : Cutoff.CutoffSample 2) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R (M.nu/(Annealed.sigmaBar M n:ℝ))
        (div_pos M.nu_pos (Annealed.sigmaBar M n).property)
        (sensitivityResponseCoefficientRestrict
          ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n Q ω) hR)) =
    coarseBlockMatrix (cubeSet R)
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  rw [upper_cell_restricted_book_matrix,cube_coarseMatrix_eq_open]
  exact coarseBlockMatrix_congr_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (upper_cell_initial_sensitivity_coefficient M Q n ω))

/-- The physical OLD descendant Book norm has the exact square-root depth
cost times the accepted trace majorant, without any estimate premise. -/
theorem upper_cell_physical_old_book_norm
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth (originCube 2 (n-ell)) j) :
    ‖HilbertBlockVec.applyBlockMat
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R (M.nu/(Annealed.sigmaBar M n:ℝ))
          (div_pos M.nu_pos (Annealed.sigmaBar M n).property)
          (sensitivityResponseCoefficientRestrict
            ((Annealed.sigmaBar M n:ℝ)⁻¹ • oldCutoffSkewCoefficient n (originCube 2 (n-ell)) ω) hR)))‖ ≤
      Real.sqrt ((Real.sqrt 3)^j) * (1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)) := by
  rw [upper_cell_physical_old_book_matrix,upper_cell_history_depth_cost]
  exact upper_cell_old_descendant_norm_bound M n ell ω j R hR

end
end ASDExplicitGamma.Scalar

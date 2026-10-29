module

public import ASDExplicitGamma.Native.OldSignedHistoryCongr

/-! Actual child coefficient histories equal those of the parent medium
on that child. The true physical molecular and scalar frame stay fixed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
noncomputable section

/-- The restricted true-frame coefficient is the actual parent medium
on the cell, independently of its off-cell display extension. -/
theorem old_signed_cell_frame_coefficient_ae (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hU k) =ᵐ[
      volumeMeasureOn (openCubeSet U)] responseFramePlanarCoefficientField nu sigma k := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
  unfold responseFramePlanarCoefficientField
  rw [old_signed_cell_coefficient_extension_eq Q U hU k hx]

/-- The actual child's coarse response matrix is unchanged. -/
theorem old_signed_cell_coarse_matrix_eq (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    coarseBlockMatrix (openCubeSet U)
      (responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hU k))=
    coarseBlockMatrix (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) :=
  coarseBlockMatrix_congr_of_ae_eq (old_signed_cell_frame_coefficient_ae Q U hU nu sigma k)

/-- The exact B,M,theta in the actual projection estimates are those
of the same old medium used by the signed generator's local error bill. -/
theorem old_signed_cell_histories (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let aU := responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hU k)
    oldSignedInverseHistory U aU=oldSignedInverseHistory U a ∧
      oldSignedResponseHistory U aU=oldSignedResponseHistory U a ∧
      oldSignedCorrectorHistory U aU=oldSignedCorrectorHistory U a := by
  intro a aU
  apply old_signed_histories_congr U aU a
  · exact responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
      nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k)
  · exact (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k).mono (measurableSet_openCubeSet U) hU
  · exact old_signed_cell_frame_coefficient_ae Q U hU nu sigma k

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalTrace

/-! Original-medium directional and trace identities on arbitrary subcells. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The physical directional matrix identification holds on every subcell,
with its own descendant partition and the unchanged parent coefficient. -/
theorem old_hessian_restricted_physical_directional_matrix (M : ABKModel 2) (n m : ℤ)
    (P : TriadicCube 2) (hP : openCubeSet P⊆openCubeSet (originCube 2 n))
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    oldSignedPairedDepthMatrix P j
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m ω))=
      descendantsAverageMat P j (fun U => oldSignedCoarseDirectionalMatrix U
        (Model.partialInsertedCoefficient M m 0 ω).toFun (Annealed.sigmaBar M m)) := by
  rw [old_hessian_paired_depth_matrix_average]
  ext i l
  unfold descendantsAverageMat descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [old_hessian_old_open_coarse_frame M n m ω U
    ((openCubeSet_subset_of_mem_descendantsAtDepth hU).trans hP)]
  have he : (Model.partialInsertedCoefficient M m 0 ω).toFun=
      (Cutoff.coefficientCutoff M.nu m ω).toFun := by
    funext x
    exact old_hessian_partial_zero M m ω x
  rw [he]
  rfl

/-- The physical trace identification also holds for the complete tiling
inside every actual subcell, without moving the medium or its frame. -/
theorem old_hessian_restricted_trace_sequence (M : ABKModel 2) (n m : ℤ)
    (P : TriadicCube 2) (hP : openCubeSet P⊆openCubeSet (originCube 2 n))
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage P j (fun U => traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m ω)) 1)=rawWeakTraceSequence M m P 0 ω j := by
  change _=oldSignedCellAverage P j (fun U => rawCubeFourLoadTrace M m U.val 0 ω)
  rw [old_signed_cell_average_eq_descendantsAverage P j (fun U => rawCubeFourLoadTrace M m U 0 ω)]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  exact old_hessian_old_open_trace_eq M n m ω U
    ((openCubeSet_subset_of_mem_descendantsAtDepth hU).trans hP)

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellBudget
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchWeak

/-! The coarse mixed comparison keeps the original fine inverse history.
The paired cell energy sums exactly to its actual coarse patch drop. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- First and reciprocal weak energies of the actual coarse comparisons,
measured on their actual fine descendants, share one actual coarse patch drop. -/
theorem old_hessian_coarse_comparison_paired_fine (Q : TriadicCube 2) (coarse refinement : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedCellAverage Q coarse (fun D =>
      let W := oldHessianParentCellComparison Q D.val
        (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P
      lemmaVTiledWeakEnergy D.val refinement W.potential+
        lemmaVTiledWeakEnergy D.val refinement (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2)) ≤
      oldHessianFineInverseHistory Q (coarse+refinement) nu sigma k*
        oldHessianPatchDrop Q coarse nu sigma hnu hsigma k P := by
  intro a
  let B := oldHessianFineInverseHistory Q (coarse+refinement) nu sigma k
  have hlocal (D : OldSignedCellIndex Q coarse) :
      let W := oldHessianParentCellComparison Q D.val
        (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P
      lemmaVTiledWeakEnergy D.val refinement W.potential+
        lemmaVTiledWeakEnergy D.val refinement (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) ≤
          B*blockPairingAverage (openCubeSet D.val) a W W := by
    let hD := openCubeSet_subset_of_mem_descendantsAtDepth D.property
    exact old_hessian_paired_response_tiled_weak D.val refinement
      ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k).mono (measurableSet_openCubeSet D.val) hD) _
      (old_hessian_parent_cell_comparison_response Q D.val hD nu sigma hnu hsigma k P)
      (old_hessian_parent_cell_comparison_memL2 Q D.val hD nu sigma hnu hsigma k P) B
      (fun U hU => old_hessian_fine_history_le Q (coarse+refinement) nu sigma k U
        (mem_descendantsAtDepth_add D.property hU))
  have hh := old_signed_cell_average_mono Q coarse hlocal
  rw [old_hessian_patch_drop_parent_partition]
  convert hh using 1
  dsimp only [B,a]
  unfold oldSignedCellAverage
  simp only [Finset.mul_sum]
  ring

end
end ASDExplicitGamma.Scalar

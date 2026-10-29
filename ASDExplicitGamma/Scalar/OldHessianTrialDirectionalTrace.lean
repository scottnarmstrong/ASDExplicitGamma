module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTrace
public import ASDExplicitGamma.Native.OldSignedDescendantDirectionalMean
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation

/-! Actual directional coarse traces on the large OLD scalar parent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The paired directional matrix is the genuine average of its child
surplus matrices, with the affine identity subtracted exactly once. -/
theorem old_hessian_paired_depth_matrix_average (Q : TriadicCube 2) (j : ℕ) (a : CoeffField 2) :
    oldSignedPairedDepthMatrix Q j a=descendantsAverageMat Q j (fun U =>
      (coarseBlockMatrix (openCubeSet U) a).upperLeft+
        (coarseBlockMatrix (openCubeSet U) a).lowerRight-(2:ℝ) • (1:Mat 2)) := by
  ext i l
  dsimp only [oldSignedPairedDepthMatrix,descendantsAverageBlockMat,descendantsAverageMat]
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [old_signed_descendants_average_sub,descendantsAverage_add,descendantsAverage_const]
  rfl

end
end ASDExplicitGamma.Scalar

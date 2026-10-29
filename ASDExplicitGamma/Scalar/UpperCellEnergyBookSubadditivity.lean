module

public import ASDExplicitGamma.Scalar.UpperCellEnergyGaugeComparison
public import ASDExplicitGamma.Variational.Subadditivity

/-! Actual coefficient restriction and parent-cell subadditivity for the
Book matrix used by the upper sensitivity comparisons. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic
noncomputable section

/-- The restricted Book matrix is the response of the same root coefficient
on the descendant, not a newly extended or resampled medium. -/
theorem upper_cell_restricted_book_matrix
    {Q R : TriadicCube 2} {j : ℕ} (nu : ℝ) (hnu : 0<nu)
    (k : ResponseCoefficient (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R nu hnu (sensitivityResponseCoefficientRestrict k hR)) =
    coarseBlockMatrix (openCubeSet R) (responseFramePlanarCoefficientField nu 1 k) := by
  rw [upper_cell_book_matrix_unit_frame]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [sensitivityResponseCoefficientRestrict_extension_ae k hR] with x hx
  rw [responseFramePlanarCoefficientField_apply,responseFramePlanarCoefficientField_apply,hx]

/-- Uniform actual descendant quadratic bounds transfer to the parent by
coarse subadditivity, with no loss and the same doubled loading. -/
theorem upper_cell_book_subadditivity_bound
    (Q : TriadicCube 2) (j : ℕ) (nu : ℝ) (hnu : 0<nu)
    (k : ResponseCoefficient (openCubeSet Q)) (K : ℝ) (P : BlockVec 2)
    (hcap : ∀ (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j),
      blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R nu hnu (sensitivityResponseCoefficientRestrict k hR))) P) ≤
        K*blockVecDot P P) :
    blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu k)) P) ≤
      K*blockVecDot P P := by
  let a := responseFramePlanarCoefficientField nu 1 k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu 1 hnu one_pos k
  have hs := cube_coarse_matrix_subadditive Q j a hEll P
  have havg := blockVecDot_blockMatVecMul_descendantsAverageBlockMat Q j
    (fun R => coarseBlockMatrix (openCubeSet R) a) P P
  rw [havg] at hs
  have hc : descendantsAverage Q j (fun R =>
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P)) ≤
      K*blockVecDot P P := by
    rw [←descendantsAverage_const Q j (K*blockVecDot P P)]
    apply descendantsAverage_le_descendantsAverage
    intro R hR
    simpa only [upper_cell_restricted_book_matrix nu hnu k hR] using hcap R hR
  rw [upper_cell_book_matrix_unit_frame]
  change blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤ _
  linarith only [hs,hc]

/-- Restriction of the parent-centered endpoint differs from the locally
centered endpoint by exactly childMean-parentMean. -/
theorem upper_cell_recentered_path_restriction
    {Q R : TriadicCube 2} {j : ℕ}
    (k kH : ResponseCoefficient (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j)
    (parentMean childMean : ℝ) :
    sensitivityResponseCoefficientRestrict
      (sensitivityResponseCoefficientPath k
        (kH+BoundedContinuousFunction.const (closure (openCubeSet Q)) (-parentMean)) 1) hR =
    sensitivityResponseCoefficientPath (sensitivityResponseCoefficientRestrict k hR)
      (sensitivityResponseCoefficientRestrict kH hR+
        BoundedContinuousFunction.const (closure (openCubeSet R)) (-childMean)) 1+
      BoundedContinuousFunction.const (closure (openCubeSet R)) (childMean-parentMean) := by
  rw [sensitivityResponseCoefficientRestrict_path,sensitivityResponseCoefficientRestrict_add_const]
  simp only [sensitivityResponseCoefficientPath,one_smul]
  ext x
  simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.const_apply]
  ring

end
end ASDExplicitGamma.Scalar

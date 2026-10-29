module

public import ASDExplicitGamma.Scalar.UpperCellEnergyGaugeMagnitude
public import ASDExplicitGamma.Scalar.UpperCellEnergyPrincipalGauge
public import ASDExplicitGamma.Scalar.UpperCellEnergyCoefficientPath

/-! Transfer a local centered Book comparison to a different constant gauge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic
noncomputable section

/-- The Book coefficient at unit frame agrees with the physical response. -/
theorem upper_cell_book_matrix_unit_frame
    (Q : TriadicCube 2) (nu : ℝ) (hnu : 0<nu)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu k) =
      coarseBlockMatrix (openCubeSet Q) (responseFramePlanarCoefficientField nu 1 k) := by
  simpa only [div_one,inv_one,one_smul] using
    upper_cell_normalized_book_matrix Q nu 1 hnu one_pos k

/-- Constant skew changes transport the Book quadratic by the literal shear
of the full doubled load. -/
theorem upper_cell_book_gauge_quadratic
    (Q : TriadicCube 2) (nu : ℝ) (hnu : 0<nu)
    (k : ResponseCoefficient (openCubeSet Q)) (g : ℝ) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu
        (k+BoundedContinuousFunction.const (closure (openCubeSet Q)) g))) P) =
    blockVecDot (constantSkewLoad g P) (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu k))
      (constantSkewLoad g P)) := by
  rw [upper_cell_book_matrix_unit_frame,upper_cell_book_matrix_unit_frame]
  have hh := upper_cell_principal_constant_gauge Q nu 1 hnu one_pos k g P
  dsimp only at hh
  rw [upper_cell_constant_projection_energy,upper_cell_constant_projection_energy] at hh
  simpa only [one_mul] using hh

/-- The centered comparison plus a controlled gauge difference has the exact
source polynomial cost for every doubled load. This is an analytic helper;
its comparison and gauge premises are discharged by the descendant estimates. -/
theorem upper_cell_gauge_transfer_comparison
    (Q : TriadicCube 2) (nu : ℝ) (hnu : 0<nu)
    (kold knew : ResponseCoefficient (openCubeSet Q))
    (C F g : ℝ) (hC : 0≤C) (hF : 0≤F) (hg : |g|≤2*F)
    (hc : BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu knew))
      (sensitivityBlockScale C
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu kold))))
    (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu
        (knew+BoundedContinuousFunction.const (closure (openCubeSet Q)) g))) P) ≤
      C*‖HilbertBlockVec.applyBlockMat
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu kold))‖*
        (1+2*F+4*F^2)*blockVecDot P P := by
  rw [upper_cell_book_gauge_quadratic]
  have hh := hc (constantSkewLoad g P)
  rw [sensitivityBlockScale_quadratic] at hh
  have hn := block_quadratic_le_operator_norm
    (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu kold))
    (constantSkewLoad g P)
  have ht := mul_le_mul_of_nonneg_left hn hC
  have hg' := mul_le_mul_of_nonneg_left (upper_cell_gauge_magnitude_of_bound g F hF hg P)
    (mul_nonneg hC (norm_nonneg (HilbertBlockVec.applyBlockMat
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q nu hnu kold)))))
  nlinarith only [hh,ht,hg']

end
end ASDExplicitGamma.Scalar

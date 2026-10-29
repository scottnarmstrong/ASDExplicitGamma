module

public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedCanonicalVariationPairing
public import ASDExplicitGamma.Native.OldSignedCellHistories

/-! Exact identification of the constant-input cell residuals used in
parent-versus-patch energy comparisons. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar
noncomputable section

/-- The actual Hilbert class of a constant field is the realization's
constant affine datum. -/
theorem old_signed_constant_field_class (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    toHilbertBlockL2OfBlockField (U := openCubeSet Q) (F := fun _ => P) (memLp_const P)=
      (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := openCubeSet Q) (memLp_const P),
    coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) P] with x hx hy
  exact hx.trans hy.symm

/-- A constant cell input gives that cell's actual affine canonical field. -/
theorem old_signed_affine_cell_residual (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedCellResidual Q U hU nu sigma hnu hsigma k (fun _ => P) (memLp_const P)=
      oldSignedFrameCanonicalField U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k) P := by
  change scalarResidualField U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k)
    (toHilbertBlockL2OfBlockField (U := openCubeSet U) (F := fun _ => P) (memLp_const P))=_
  rw [old_signed_constant_field_class U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k) P,
    old_signed_affine_residual_field]
  rfl

/-- Its exact local energy is the actual parent coefficient's coarse
quadratic form on that cell; extension choices do not change it. -/
theorem old_signed_affine_cell_energy (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let R := oldSignedCellResidual Q U hU nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hU k) R R=
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k)) P) := by
  intro R
  dsimp only [R]
  rw [old_signed_affine_cell_residual,old_signed_canonical_energy,
    old_signed_cell_coarse_matrix_eq]

end
end ASDExplicitGamma.Native

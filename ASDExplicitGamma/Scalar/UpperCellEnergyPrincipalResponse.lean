module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetMean
public import ASDExplicitGamma.Scalar.UpperCellEnergyProjection
public import ASDExplicitGamma.Scalar.UpperCellEnergyMeasurability
public import ASDExplicitGamma.Native.OldSignedCanonicalVariationPairing

/-! The principal UPPER projection is the actual affine coarse response at the cell mean. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Native MeasureTheory
open Algsuperdiff.Section3
noncomputable section

/-- Projecting a constant load gives the genuine canonical affine minimizer. -/
theorem upper_cell_constant_projection_eq_minimizer
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    scalarProjectionResidual Q nu sigma hnu hsigma k
      (blockVecToHilbertBlockL2Const (U := openCubeSet Q) P) =
      (scalarFrameRealization Q nu sigma hnu hsigma k).minimizerMap P := by
  rw [scalarProjectionResidual_eq_affineMinimizer]
  rfl

/-- The exact Hilbert energy of the constant-load projection is its physical
coarse response quadratic. This retains the normalized physical coefficient. -/
theorem upper_cell_constant_projection_energy
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let B := (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
    let S := scalarProjectionResidual Q nu sigma hnu hsigma k
      (blockVecToHilbertBlockL2Const (U := openCubeSet Q) P)
    B S S = blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField nu sigma k)) P) := by
  dsimp only
  rw [upper_cell_constant_projection_eq_minimizer]
  let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have he := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hS hS
  have hr : toHilbertBlockL2OfBlockField hS =
      (scalarFrameRealization Q nu sigma hnu hsigma k).minimizerMap P :=
    hilbert_field_rebuild _
  rw [hr] at he
  exact he.trans (old_signed_canonical_energy Q nu sigma hnu hsigma k P)

/-- The principal projected field of a measurable physical load is measurable
on the actual cutoff law's carrier. -/
theorem upper_cell_principal_projection_measurable
    (N : ℤ) (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hF : Measurable F) :
    Measurable (fun ω => scalarProjectionResidual Q nu sigma hnu hsigma
      (oldCutoffSkewCoefficient N Q ω) (upperCellResetMeanField Q (F ω))) :=
  upper_cell_random_projection_measurable N Q nu sigma hnu hsigma _
    (upper_cell_reset_mean_field_measurable Q F hF)

end
end ASDExplicitGamma.Scalar

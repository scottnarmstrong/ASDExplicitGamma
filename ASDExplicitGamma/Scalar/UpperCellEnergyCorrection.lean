module

public import ASDExplicitGamma.Scalar.TrialIntegrability
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Scalar.UpperCellEnergyProjection

/-! The actual UPPER weighted-cell correction for the full band load.
The existing OLD recovery theorem supplies the physical variation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The cell correction is the full weighted projection minus the full load,
represented as a physical field on the cell. -/
def upperCellCorrectionField
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    Vec 2 → BlockVec 2 :=
  hilbertBlockL2ToBlockL2 (scalarProjectionResidual Q nu sigma hnu hsigma k F - F)

/-- The actual correction has zero potential trace and zero flux normal trace. -/
theorem upper_cell_correction_variation
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    ScalarVariation (openCubeSet Q) (upperCellCorrectionField Q nu sigma hnu hsigma k F) := by
  apply Native.old_signed_hilbert_correction_variation
  have hh := (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace.toSubmodule.neg_mem
    (scalar_projection_removed_mem Q nu sigma hnu hsigma k F)
  change scalarProjectionResidual Q nu sigma hnu hsigma k F - F ∈
    (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace.toSubmodule
  simpa only [neg_sub] using hh

/-- Adding the correction to the original physical load gives the actual
weighted minimizer almost everywhere on the cell. -/
theorem upper_cell_corrected_field_eq
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) :
    F + upperCellCorrectionField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
      hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)) := by
  let X := toHilbertBlockL2OfBlockField hF
  let Z := scalarProjectionResidual Q nu sigma hnu hsigma k X
  have hX : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet Q)] F := by
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField]
    exact coeFn_toBlockL2 hF
  have hsub := Lp.coeFn_sub (hilbertBlockL2ToBlockL2 Z) (hilbertBlockL2ToBlockL2 X)
  unfold upperCellCorrectionField
  rw [map_sub]
  filter_upwards [hX,hsub] with x hx hs
  change F x + (hilbertBlockL2ToBlockL2 Z - hilbertBlockL2ToBlockL2 X) x = _
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hx]
  abel

end
end ASDExplicitGamma.Scalar

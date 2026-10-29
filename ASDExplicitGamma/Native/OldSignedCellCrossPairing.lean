module

public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Scalar.ProjectionCharacterization

/-! Exact cross-source orthogonality for actual weighted cell residuals,
used before estimating the signed A-R and Z-R cross terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
noncomputable section

/-- The two actual residuals pair exactly through the second input.
The identity uses the same weighted projection and no estimated premise. -/
theorem old_signed_residual_cross_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    let RF := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    let RG := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
    oldSignedEnergyPairing Q nu sigma k RF RG=oldSignedEnergyPairing Q nu sigma k RF G := by
  intro RF RG
  have hRF : MemBlockL2 (openCubeSet Q) RF := RF.property
  have hRG : MemBlockL2 (openCubeSet Q) RG := RG.property
  have hrF : toHilbertBlockL2OfBlockField hRF=
      scalarProjectionResidual Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF) :=
    hilbert_field_rebuild _
  have hrG : toHilbertBlockL2OfBlockField hRG=
      scalarProjectionResidual Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG) :=
    hilbert_field_rebuild _
  have hh := scalar_projection_residual_orthogonal Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hF) _
    (scalar_projection_removed_mem Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG))
  rw [map_sub] at hh
  have hpair := (sub_eq_zero.mp hh).symm
  have he := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hRG hRF
  rw [(scalarFrameRealization Q nu sigma hnu hsigma k).energySymm,hrF,hrG] at he
  have hs := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hG hRF
  rw [(scalarFrameRealization Q nu sigma hnu hsigma k).energySymm,hrF] at hs
  rw [he,hs] at hpair
  exact hpair

end
end ASDExplicitGamma.Native

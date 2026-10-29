module

public import ASDExplicitGamma.Native.OldSignedPhysicalCoefficient
public import ASDExplicitGamma.Native.OldSignedActualTrialVariation

/-! Transport of the actual plain OLD trial fields to the weighted energy
carrier used by the physical Hessian. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
noncomputable section

/-- Recover a Hilbert class from any proved plain representative. -/
theorem old_signed_hilbert_field_of_representative (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (X : HilbertBlockL2 (openCubeSet Q))
    (hX : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet Q)] F) :
    toHilbertBlockL2OfBlockField hF = X := by
  apply (continuousLinearEquivBlockL2 (U := openCubeSet Q)).symm.injective
  change hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF)=_
  rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField]
  apply Lp.ext
  exact (coeFn_toBlockL2 hF).trans hX.symm

/-- A genuine plain variation is a variation of the actual energy carrier. -/
theorem old_signed_energy_variation_of_representative (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (X : EnergyCarrier (scalarFrameEnergyData Q nu sigma hnu hsigma k))
    {F : Vec 2 → BlockVec 2}
    (hX : hilbertBlockL2ToBlockL2 X.down =ᵐ[volumeMeasureOn (openCubeSet Q)] F)
    (hF : ScalarVariation (openCubeSet Q) F) :
    X ∈ (scalarFrameVariationSpace Q nu sigma hnu hsigma k).toSubmodule := by
  change X.down ∈ (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace
  rw [←old_signed_hilbert_field_of_representative Q hF.1 X.down hX]
  exact scalar_variation_mem_frame_correction Q nu sigma hnu hsigma k hF

/-- The weighted inner product of actual fields is the literal OLD pairing. -/
theorem old_signed_energy_inner_fields (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    inner ℝ (responseEnergyUp (scalarFrameEnergyData Q nu sigma hnu hsigma k)
      (toHilbertBlockL2OfBlockField hF))
      (responseEnergyUp (scalarFrameEnergyData Q nu sigma hnu hsigma k)
        (toHilbertBlockL2OfBlockField hG)) = oldSignedEnergyPairing Q nu sigma k F G := by
  change (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin _ _=_
  rw [(scalarFrameRealization Q nu sigma hnu hsigma k).energySymm]
  exact scalar_frame_bilinear_field Q nu sigma hnu hsigma k hG hF

end
end ASDExplicitGamma.Native

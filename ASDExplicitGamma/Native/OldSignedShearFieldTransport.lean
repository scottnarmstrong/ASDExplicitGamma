module

public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Native.OldSignedReciprocalPotential

/-! Exact physical shear fields and their signed pairing with the actual
reciprocal gradient, in the same fixed-frame weighted energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual physical shear preserves parent square integrability. -/
theorem old_signed_physical_shear_field_memL2 (Q : TriadicCube 2) (sigma b : ℝ)
    (hsigma : 0<sigma) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    MemBlockL2 (openCubeSet Q)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) F) := by
  let X := toHilbertBlockL2OfBlockField hF
  have hX : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet Q)] F := by
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField]
    exact coeFn_toBlockL2 hF
  have hC := old_signed_physical_shear_representative Q sigma b hsigma L n X
  have hrep : hilbertBlockL2ToBlockL2 (responseShearL2Operator sigma hsigma
      (oldSignedPhysicalCoefficient Q sigma b L n) X) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) F := by
    filter_upwards [hC,hX] with x hx hy
    rw [hx]
    change (0,-(_ • matVecMul responsePlanarJ (hilbertBlockL2ToBlockL2 X x).1))=_
    rw [hy]
    rfl
  exact (memLp_congr_ae hrep).mp
    (hilbertBlockL2ToBlockL2 (responseShearL2Operator sigma hsigma
      (oldSignedPhysicalCoefficient Q sigma b L n) X)).property

/-- The literal physical shear has the same L2 class as the genuine
response operator, not merely a norm-bounded surrogate. -/
theorem old_signed_physical_shear_field_class (Q : TriadicCube 2) (sigma b : ℝ)
    (hsigma : 0<sigma) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    toHilbertBlockL2OfBlockField (old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hF)=
      responseShearL2Operator sigma hsigma (oldSignedPhysicalCoefficient Q sigma b L n)
        (toHilbertBlockL2OfBlockField hF) := by
  apply old_signed_hilbert_field_of_representative
  have hc := old_signed_physical_shear_representative Q sigma b hsigma L n (toHilbertBlockL2OfBlockField hF)
  have hf : hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF)=ᵐ[volumeMeasureOn (openCubeSet Q)] F := by
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField]
    exact coeFn_toBlockL2 hF
  filter_upwards [hc,hf] with x hx hy
  rw [hx]
  change (0,-(_ • matVecMul responsePlanarJ (hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF) x).1))=_
  rw [hy]
  rfl

/-- The weighted shear pairing is exactly minus the physical pairing
against the reciprocal second gradient. The sign is retained. -/
theorem old_signed_energy_physical_shear_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F G : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k F
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) G)=
      -volumeAverage (openCubeSet Q) (fun x => vecDot
        (q3Convolution b L h3Zero (whiteBasis n) x • matVecMul responsePlanarJ (G x).1)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (F x)).2) := by
  have hC := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hG
  unfold oldSignedEnergyPairing
  rw [←scalar_frame_bilinear_field Q nu sigma hnu hsigma k hC hF,
    (scalarFrameRealization Q nu sigma hnu hsigma k).energySymm,
    scalar_frame_bilinear_field Q nu sigma hnu hsigma k hF hC]
  simp only [oldSignedPointwiseShear,LinearMap.coe_mk,AddHom.coe_mk,blockVecDot,vecDot_zero_left,
    vecDot_neg_left,zero_add,volumeAverage,integral_neg]
  ring

end
end ASDExplicitGamma.Native

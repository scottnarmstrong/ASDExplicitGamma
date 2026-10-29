module

public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport

/-! Qualitative energy contraction of the actual weighted complement.
This supplies convergence without using the sharp OLD history constants. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
noncomputable section

/-- The literal weighted complementary projection contracts its energy. -/
theorem old_signed_residual_energy_contraction (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) :
    (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
      (scalarProjectionResidual Q nu sigma hnu hsigma k F)
      (scalarProjectionResidual Q nu sigma hnu hsigma k F)≤
      (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin F F := by
  let D := scalarFrameEnergyData Q nu sigma hnu hsigma k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) := scalarFrameVariationSpace Q nu sigma hnu hsigma k
  let X : EnergyCarrier D := responseEnergyUp D F
  have hp := V.toSubmodule.norm_sq_eq_add_norm_sq_starProjection X
  rw [Submodule.starProjection_orthogonal_val] at hp
  have hh : ‖X-V.toSubmodule.starProjection X‖^2≤‖X‖^2 := by
    linarith only [hp,sq_nonneg ‖V.toSubmodule.starProjection X‖]
  change (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
    (X-V.toSubmodule.starProjection X).down (X-V.toSubmodule.starProjection X).down≤_
  rw [energyCarrier_norm_sq D (X-V.toSubmodule.starProjection X),energyCarrier_norm_sq D X] at hh
  exact hh

/-- The actual field representative's energy contracts the input energy,
with membership and reconstruction proved rather than supplied. -/
theorem old_signed_residual_field_energy_contraction (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedEnergyPairing Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF))
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF))≤
      oldSignedEnergyPairing Q nu sigma k F F := by
  let S := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
  have hS : MemBlockL2 (openCubeSet Q) S := S.property
  have hr : toHilbertBlockL2OfBlockField hS=
      scalarProjectionResidual Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF) :=
    hilbert_field_rebuild _
  have hs := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hS hS
  rw [hr] at hs
  have hh := old_signed_residual_energy_contraction Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
  rw [hs,scalar_frame_bilinear_field Q nu sigma hnu hsigma k hF hF] at hh
  exact hh

/-- The input energy of a literal pure-second source has the exact
physical sigma/nu factor, independent of the old skew coefficient. -/
theorem old_signed_pure_second_input_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (g : Vec 2 → Vec 2) :
    oldSignedEnergyPairing Q nu sigma k (fun x => (0,g x)) (fun x => (0,g x))=
      (sigma/nu)*volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x)) := by
  have hp (x : Vec 2) : blockVecDot (0,g x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (0,g x))=
      (sigma/nu)*vecNormSq (g x) := by
    have he : responseFrameEnergyDensity nu sigma (responseCoefficientExtension k x) (0,g x)=
        blockVecDot (0,g x) (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (0,g x)) :=
      responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma (responseCoefficientExtension k x) hnu hsigma _
    rw [←he]
    simp only [responseFrameEnergyDensity,matVecMul_zero,smul_zero,sub_zero,
      vecNormSq,vecDot_zero_left,mul_zero,zero_add]
  unfold oldSignedEnergyPairing
  simp_rw [hp]
  change volumeAverage (openCubeSet Q) ((sigma/nu) • (fun x => vecNormSq (g x)))=_
  rw [volumeAverage_smul]

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Native.BoundaryChargeSignedTrial

/-! AN (4.2) for the physical OLD coefficient direction, transported from
proved plain trial membership to the genuine weighted Hessian carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Plain admissibility supplies the actual physical signed Hessian trial.
This internal helper retains the signed feedback and the frame scale. -/
theorem old_signed_physical_trial_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (htrial : ScalarVariation (openCubeSet Q)
      (F-oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))) :
    let hU := measurableSet_openCubeSet Q
    let hv : 0<(volume (openCubeSet Q)).toReal := by
      rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
    let D := responseFrameEnergyData hU hv nu sigma hnu hsigma k
    let H := oldSignedPhysicalCoefficient Q sigma b L n
    let C := responseFrameEnergyShearFamily hU hv nu sigma hnu hsigma k
    let S := responseFrameEnergyBaseMinimizer hU hv nu sigma hnu hsigma k P
    let R := responseEnergyUp D (toHilbertBlockL2OfBlockField hF)
    (1/2:ℝ)*fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hv nu sigma hnu hsigma P) z H) k H ≤
      ‖R‖^2+2*inner ℝ S (C H R) := by
  intro hU hv D H C S R
  apply native_boundary_signed_response_trial hU hv nu sigma hnu hsigma P k H R
  have hR : hilbertBlockL2ToBlockL2 R.down =ᵐ[volumeMeasureOn (openCubeSet Q)] F := by
    change hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF)=ᵐ[_] F
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField]
    exact coeFn_toBlockL2 hF
  have hC : hilbertBlockL2ToBlockL2 (C H S).down =ᵐ[volumeMeasureOn (openCubeSet Q)]
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) := by
    change hilbertBlockL2ToBlockL2
      (responseShearL2Operator sigma hsigma H S.down)=ᵐ[_] _
    exact old_signed_physical_shear_representative Q sigma b hsigma L n S.down
  apply old_signed_energy_variation_of_representative Q nu sigma hnu hsigma k (R-(show EnergyCarrier D from C H S)) _ htrial
  change hilbertBlockL2ToBlockL2 (R.down-(C H S).down)=ᵐ[_] _
  have hm := (continuousLinearEquivBlockL2 (U := openCubeSet Q)).symm.map_sub R.down (C H S).down
  change hilbertBlockL2ToBlockL2 (R.down-(C H S).down)=
    hilbertBlockL2ToBlockL2 R.down-hilbertBlockL2ToBlockL2 (C H S).down at hm
  rw [hm]
  exact (Lp.coeFn_sub _ _).trans (hR.sub hC)

end
end ASDExplicitGamma.Native

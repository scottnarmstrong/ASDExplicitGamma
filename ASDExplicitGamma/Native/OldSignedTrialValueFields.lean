module

public import ASDExplicitGamma.Native.OldSignedActualHessianTrial
public import ASDExplicitGamma.Native.OldSignedShearFieldTransport

/-! The actual Hilbert signed trial value is its literal normalized
physical field energy and physical shear feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian
noncomputable section

/-- Exact field form of the signed physical trial value. Every class
identification uses the same actual representative and coefficient. -/
theorem old_signed_trial_value_fields (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k P b L n hF=
      oldSignedEnergyPairing Q nu sigma k F F+2*oldSignedEnergyPairing Q nu sigma k
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
        (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) F) := by
  let D := scalarFrameEnergyData Q nu sigma hnu hsigma k
  let H := oldSignedPhysicalCoefficient Q sigma b L n
  let R : EnergyCarrier D := responseEnergyUp D (toHilbertBlockL2OfBlockField hF)
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) nu sigma hnu hsigma k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) nu sigma hnu hsigma k
  have hn : ‖R‖^2=oldSignedEnergyPairing Q nu sigma k F F := by
    have hh := old_signed_energy_inner_fields Q nu sigma hnu hsigma k hF hF
    rw [real_inner_self_eq_norm_sq] at hh
    exact hh
  let hS : MemBlockL2 (openCubeSet Q) (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) :=
    Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
  let hCF := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hF
  have hs : toHilbertBlockL2OfBlockField hS=S.down := hilbert_field_rebuild _
  have hi := old_signed_energy_inner_fields Q nu sigma hnu hsigma k hS hCF
  rw [hs,old_signed_physical_shear_field_class Q sigma b hsigma L n hF] at hi
  have hifield : inner ℝ S (C H R)=oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) F) := hi
  change ‖R‖^2+2*inner ℝ S (C H R)=_
  rw [hn,hifield]

end
end ASDExplicitGamma.Native

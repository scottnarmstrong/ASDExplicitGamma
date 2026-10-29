module

public import ASDExplicitGamma.Native.OldSignedCanonicalShearPairing

/-! The parent reciprocal potential restricted to each actual cell, with
the same coefficient and exact signed weighted shear pairing on that cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Restrict the genuine parent reciprocal potential, preserving all old
coefficient correlations rather than replacing it by a cell solution. -/
def oldSignedCellReciprocalPotential (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) : H1Function (openCubeSet U) :=
  (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k P).restrict (isOpen_openCubeSet U) hU

/-- On a cell this restricted parent gradient is the second block of the
same parent minimizer under the actual restricted coefficient. -/
theorem old_signed_cell_reciprocal_potential_grad (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedCellReciprocalPotential Q U hU nu sigma hnu hsigma k P).grad =ᵐ[volumeMeasureOn (openCubeSet U)]
      fun x => (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hU k)) x)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2 := by
  have hg := ae_restrict_of_ae_restrict_of_subset hU
    (old_signed_frame_reciprocal_potential_grad Q nu sigma hnu hsigma k P)
  filter_upwards [hg,ae_restrict_mem (measurableSet_openCubeSet U)] with x hx hmem
  change (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k P).grad x=_
  rw [hx]
  have hc : responseFramePlanarCoefficientField nu sigma k x=
      responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hU k) x := by
    unfold responseFramePlanarCoefficientField
    rw [old_signed_cell_coefficient_extension_eq Q U hU k hmem]
  unfold blockCoeffField
  rw [hc]

/-- The actual cell feedback tests the restricted parent reciprocal
gradient, including its true boundary data on this cell. -/
theorem old_signed_cell_canonical_shear_pairing (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet U) F) :
    oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hU k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) F)=
      -volumeAverage (openCubeSet U) (fun x => vecDot
        (q3Convolution b L h3Zero (whiteBasis n) x • matVecMul responsePlanarJ (F x).1)
        ((oldSignedCellReciprocalPotential Q U hU nu sigma hnu hsigma k P).grad x)) := by
  have hS : MemBlockL2 (openCubeSet U) (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) :=
    (show MemBlockL2 (openCubeSet Q) (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) from
      Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)).mono_measure
        (Measure.restrict_mono_set volume hU)
  rw [old_signed_energy_physical_shear_pairing U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hU k) b L n hS hF]
  congr 1
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [old_signed_cell_reciprocal_potential_grad Q U hU nu sigma hnu hsigma k P] with x hx
  rw [hx]

end
end ASDExplicitGamma.Native

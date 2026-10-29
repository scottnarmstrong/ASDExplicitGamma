module

public import ASDExplicitGamma.Native.OldSignedEnergyPartition

/-! Split the bottom flat tangent before partitioning the correction.
This keeps the signed global covariance term intact. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Actual patched feedback equals the actual global flat feedback plus
cell correction feedback. The same parent field is retained in every cell. -/
theorem old_signed_patched_correction_feedback_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) {S F : Vec 2 → BlockVec 2}
    (hS : MemBlockL2 (openCubeSet Q) S) (hF : MemBlockL2 (openCubeSet Q) F) :
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    oldSignedEnergyPairing Q nu sigma k S
      (C (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF))=
    oldSignedEnergyPairing Q nu sigma k S (C F)+
    oldSignedCellAverage Q depth (fun U => oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) S
      (C ((oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F hF : Vec 2 → BlockVec 2)-F))) := by
  intro C
  let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  have hR := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hCR := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hR
  have hCF := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hF
  have hsplit : oldSignedEnergyPairing Q nu sigma k S (C R)=
      oldSignedEnergyPairing Q nu sigma k S (C F)+
      oldSignedEnergyPairing Q nu sigma k S (C (R-F)) := by
    rw [map_sub,old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hS hCR hCF]
    ring
  rw [hsplit]
  congr 1
  rw [old_signed_energy_pairing_partition Q depth nu sigma hnu hsigma k hS
    (old_signed_physical_shear_field_memL2 Q sigma b hsigma L n (hR.sub hF))]
  congr 1
  funext U
  apply old_signed_energy_pairing_congr_ae U.val nu sigma _ Filter.EventuallyEq.rfl
  apply old_signed_pointwise_shear_congr_ae
  exact (old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k F hF U.val U.property).sub
    Filter.EventuallyEq.rfl

end
end ASDExplicitGamma.Native

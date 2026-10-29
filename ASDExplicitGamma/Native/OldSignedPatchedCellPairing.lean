module

public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra

/-! Exact spatial identities for the actual weighted residuals, retaining the
true restricted coefficient on each physical cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar
noncomputable section

/-- The parent pairing of the two actual patched residuals is the normalized
finite average of the pairings of their actual cell projections. -/
theorem old_signed_local_residual_cell_pairing (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG)=
    oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F hF)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k G hG)) := by
  classical
  rw [old_signed_local_residual_energy]
  rw [← old_signed_cell_average_eq_descendantsAverage]
  congr 1
  funext U
  unfold oldSignedEnergyPairing volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards
    [old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k F hF U.val U.property,
     old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k G hG U.val U.property,
     old_signed_cell_frame_coefficient_ae Q U.val
       (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma k] with x hFx hGx ha
  simp only [hFx,hGx,blockCoeffField,← ha]

end
end ASDExplicitGamma.Native

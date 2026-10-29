module

public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Native.OldSignedOldSourceBudget
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! Complete spatial assembly of the actual four-load OLD-source energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- The four-load patched OLD-source energy is summable and bounded by
the actual average of B_U d_U squared. -/
theorem old_signed_global_old_source_energy_bill (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let R := fun n c => oldSignedPatchedOldError Q depth depth nu sigma hnu hsigma k b L n (blockBasis c)
    let f := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing Q nu sigma k (R n c) (R n c)
    Summable f ∧ (∑' n,f n)≤descendantsAverage Q depth (fun U =>
      oldSignedInverseHistory U a*oldSignedOldSourceSize Q U depth nu sigma hnu hsigma k b L^2) := by
  intro Q a R f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    let R := fun c => oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k
      (oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (blockBasis c))
      (old_signed_frame_old_error_source_memL2 Q depth nu sigma hnu hsigma k b L n (blockBasis c))
    ∑ c : BlockCoord 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (R c) (R c)
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    change (∑ c : BlockCoord 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k _ _)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k _ _))=_
    simp_rw [old_signed_local_residual_cell_pairing]
    rw [old_signed_cell_average_sum]
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_upper Q depth fc _
    (fun U => (old_signed_actual_old_source_budget m depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => (old_signed_actual_old_source_budget m depth nu sigma hnu hsigma k b L U.val U.property).2.1)

end
end ASDExplicitGamma.Native

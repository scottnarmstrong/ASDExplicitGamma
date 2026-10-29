module

public import ASDExplicitGamma.Native.OldSignedMixedPartition
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Native.OldSignedMixedFeedbackBill
public import ASDExplicitGamma.Native.OldSignedFlatPatchedData

/-! Complete spatial assembly of the two mixed remainders, retaining
their unprojected physical flat pairings for the covariance terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- The complete actual A-R or Z-R remainder has the exact averaged
joint local bill; no local estimate or convergence is assumed. -/
theorem old_signed_global_mixed_feedback_bill (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let F := fun n i => oldSignedFlatInput Q b L plus n i
    let H := fun n i => oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)
    let f := fun n => ∑ i : Fin 2,
      (oldSignedEnergyPairing Q nu sigma k
        (oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i)
        (oldSignedPatchedOldError Q depth depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))-
        volumeAverage (openCubeSet Q) (fun x => vecDot (F n i x).2 (H n i x).2))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedOldSourceSize Q U depth nu sigma hnu hsigma k b L*
      (Real.sqrt (6*oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L plus+
        (oldSignedResponseHistory U a+1)*oldSignedFlatOscillationSize Q U b L plus)) := by
  intro Q a F H f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,
      (oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U.val U.property)
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (H n i)
          (old_signed_frame_old_error_source_memL2 Q depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i)))-
        volumeAverage (openCubeSet U.val) (fun x => vecDot (F n i x).2 (H n i x).2))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_mixed_pairing_load_partition Q depth nu sigma hnu hsigma k (F n) (H n)
      (old_signed_flat_input_memL2 Q b L plus n)
      (fun i => old_signed_frame_old_error_source_memL2 Q depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i))
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (old_signed_actual_mixed_feedback_bill m depth nu sigma hnu hsigma k b L plus U.val U.property).1)
    (fun U => (old_signed_actual_mixed_feedback_bill m depth nu sigma hnu hsigma k b L plus U.val U.property).2)

end
end ASDExplicitGamma.Native

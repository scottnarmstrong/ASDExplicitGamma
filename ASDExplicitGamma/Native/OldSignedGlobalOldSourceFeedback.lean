module

public import ASDExplicitGamma.Native.OldSignedFeedbackLoadPartition
public import ASDExplicitGamma.Native.OldSignedOldSourceFeedbackBill
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! The complete physical four-load OLD-source derivative feedback, after exact spatial
assembly. All local old-medium factors remain jointly averaged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- The actual parent OLD-source feedback is genuinely summable and obeys the
exact average of the local AN derivative bills. -/
theorem old_signed_global_old_source_feedback_bill (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => ∑ i : BlockCoord 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedPatchedOldError Q depth depth nu sigma hnu hsigma k b L n (blockBasis i)))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        oldSignedOldSourceSize Q U depth nu sigma hnu hsigma k b L)) := by
  intro Q a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : BlockCoord 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (blockBasis i))
          (old_signed_frame_old_error_source_memL2 Q depth nu sigma hnu hsigma k b L n (blockBasis i))))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_patched_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : BlockCoord 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (fun i => oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (blockBasis i)) (fun _ => Lp.memLp _)
      (fun i => old_signed_frame_old_error_source_memL2 Q depth nu sigma hnu hsigma k b L n (blockBasis i))
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (old_signed_actual_old_source_feedback_bill m depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => (old_signed_actual_old_source_feedback_bill m depth nu sigma hnu hsigma k b L U.val U.property).2)

end
end ASDExplicitGamma.Native

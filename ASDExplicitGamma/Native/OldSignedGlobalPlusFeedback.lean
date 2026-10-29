module

public import ASDExplicitGamma.Native.OldSignedFeedbackLoadPartition
public import ASDExplicitGamma.Native.OldSignedPlusFeedbackBill
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! The complete physical top derivative feedback, after exact spatial
assembly. All local old-medium factors remain jointly averaged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- The actual parent top feedback is genuinely summable and obeys the
exact average of the local AN derivative bills. -/
theorem old_signed_global_plus_feedback_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k*
      (Real.sqrt (oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L true+
        (1+inverseHistoryDiscount)*oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true)) := by
  intro a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (oldSignedFlatPlusBlock Q b L n i)
          (old_signed_flat_plus_block_memL2 Q b L n i)))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_patched_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : Fin 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedFlatPlusBlock Q b L n) (fun _ => Lp.memLp _)
      (old_signed_flat_plus_block_memL2 Q b L n)
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (old_signed_actual_plus_feedback_bill Q depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => (old_signed_actual_plus_feedback_bill Q depth nu sigma hnu hsigma k b L U.val U.property).2)

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedFeedbackLoadPartition
public import ASDExplicitGamma.Native.OldSignedMinusFeedbackDirectionalBill
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! Spatial assembly of the complete bottom correction feedback. The
flat tangent is excluded here and retains its exact signed covariance bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- The actual bottom feedback minus its global flat tangent has precisely
the averaged minus-correction bill of AN. -/
theorem old_signed_global_minus_feedback_directional_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let C := fun n => oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := fun i => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inr i))
    let f := fun n => (∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k (S i)
      (C n (oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i)))-
      ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k (S i) (C n (oldSignedFlatMinusBlock Q b L n i))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      (Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L false)+
        (Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1)*oldSignedFlatOscillationSize Q U b L false)) := by
  intro a C S f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (S i) (C n ((oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L n i)
        (old_signed_flat_minus_block_memL2 Q b L n i) : Vec 2 → BlockVec 2)-oldSignedFlatMinusBlock Q b L n i))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    have hh := old_signed_patched_correction_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : Fin 2 => S i) (oldSignedFlatMinusBlock Q b L n) (fun i => Lp.memLp (S i))
      (old_signed_flat_minus_block_memL2 Q b L n)
    change _=_+oldSignedCellAverage Q depth (fc n) at hh
    change _-_=_
    exact sub_eq_iff_eq_add.mpr (hh.trans (add_comm _ _))
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (old_signed_actual_minus_feedback_directional_bill Q depth nu sigma hnu hsigma k b L U.val U.property).1)
    (fun U => by
      have hh := (old_signed_actual_minus_feedback_directional_bill Q depth nu sigma hnu hsigma k b L U.val U.property).2
      have he := old_signed_flat_directional_proxy_cell_eq Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k b L false
      simp only [oldSignedFlatDirectionalMeanProxy,oldSignedFlatInput,
        Bool.false_eq_true,ite_false] at he
      dsimp only at hh
      rw [he] at hh
      exact hh)

end
end ASDExplicitGamma.Native

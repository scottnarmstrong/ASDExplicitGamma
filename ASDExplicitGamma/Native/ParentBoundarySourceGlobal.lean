module

public import ASDExplicitGamma.Native.ParentBoundarySourceFeedback
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Native.OldSignedFeedbackLoadPartition
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound

/-! Complete physical spatial assembly of the parent source energy and
its derivative feedback, retaining every joint cell factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- Complete parent source energy on the actual finite comparison partition. -/
theorem parent_boundary_global_source_energy (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let R := fun n c => parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (blockBasis c)
    let f := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing Q nu sigma k (R n c) (R n c)
    Summable f ∧ (∑' n,f n)≤descendantsAverage Q depth (fun U =>
      oldSignedInverseHistory U a*parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L^2) := by
  intro Q a R f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    let R := fun c => oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k
      (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c))
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis c))
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
    (fun U => (parent_boundary_cell_source_budget Q U.val depth U.property nu sigma hnu hsigma k b L).1)
    (fun U => (parent_boundary_cell_source_budget Q U.val depth U.property nu sigma hnu hsigma k b L).2.1)


/-- Complete parent source feedback on the actual finite comparison partition. -/
theorem parent_boundary_global_source_feedback (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => ∑ i : BlockCoord 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (blockBasis i)))
    Summable f ∧ |∑' n,f n|≤descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L)) := by
  intro Q a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : BlockCoord 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis i))
          (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis i))))
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_patched_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : BlockCoord 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (fun i => parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis i)) (fun _ => Lp.memLp _)
      (fun i => parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis i))
  rw [he,← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (parent_boundary_cell_source_feedback Q U.val depth U.property nu sigma hnu hsigma k b L).1)
    (fun U => (parent_boundary_cell_source_feedback Q U.val depth U.property nu sigma hnu hsigma k b L).2)


end
end ASDExplicitGamma.Native

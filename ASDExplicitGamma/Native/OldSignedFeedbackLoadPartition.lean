module

public import ASDExplicitGamma.Native.OldSignedCorrectionPartition
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound

/-! Finite physical load sums of the spatial feedback identities. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- The full chosen load sum of patched feedback is the average of the
same actual load sum on each cell. -/
theorem old_signed_patched_feedback_load_partition {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (S F : I → Vec 2 → BlockVec 2)
    (hS : ∀ i,MemBlockL2 (openCubeSet Q) (S i))
    (hF : ∀ i,MemBlockL2 (openCubeSet Q) (F i)) :
    (∑ i,oldSignedEnergyPairing Q nu sigma k (S i)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i))))=
    oldSignedCellAverage Q depth (fun U => ∑ i,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (S i)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i)))) := by
  simp_rw [old_signed_patched_feedback_partition Q depth nu sigma hnu hsigma k b L n (hS _) (hF _)]
  rw [old_signed_cell_average_sum]

/-- The full bottom-load feedback splits into the global signed flat
term and the cellwise correction terms before their complete-mode bounds. -/
theorem old_signed_patched_correction_feedback_load_partition {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (S F : I → Vec 2 → BlockVec 2)
    (hS : ∀ i,MemBlockL2 (openCubeSet Q) (S i))
    (hF : ∀ i,MemBlockL2 (openCubeSet Q) (F i)) :
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    (∑ i,oldSignedEnergyPairing Q nu sigma k (S i)
      (C (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i))))=
    (∑ i,oldSignedEnergyPairing Q nu sigma k (S i) (C (F i)))+
    oldSignedCellAverage Q depth (fun U => ∑ i,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (S i)
      (C ((oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i) : Vec 2 → BlockVec 2)-F i))) := by
  intro C
  dsimp only [C]
  simp_rw [old_signed_patched_correction_feedback_partition Q depth nu sigma hnu hsigma k b L n (hS _) (hF _)]
  rw [Finset.sum_add_distrib,old_signed_cell_average_sum]

end
end ASDExplicitGamma.Native

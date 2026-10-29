module

public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing

/-! Exact partition of the mixed remainder, keeping the unprojected
flat/source pairing for the global covariance calculation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar
noncomputable section

/-- The mixed pairing remainder partitions exactly with the actual cell
projections and the same unprojected physical input pairing. -/
theorem old_signed_mixed_pairing_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG)-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (G x).2)=
    oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k F hF)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k G hG)-
      volumeAverage (openCubeSet U.val) (fun x => vecDot (F x).2 (G x).2)) := by
  have hp := old_signed_volumeAverage_descendants Q depth _
    (integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF)
      (memVectorL2_snd_of_memBlockL2 hG))
  rw [old_signed_local_residual_cell_pairing,hp,
    ← old_signed_cell_average_eq_descendantsAverage,old_signed_cell_average_sub]

/-- Finite canonical load sums commute with the exact mixed partition. -/
theorem old_signed_mixed_pairing_load_partition {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : I → Vec 2 → BlockVec 2)
    (hF : ∀ i,MemBlockL2 (openCubeSet Q) (F i))
    (hG : ∀ i,MemBlockL2 (openCubeSet Q) (G i)) :
    (∑ i,(oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (G i) (hG i))-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F i x).2 (G i x).2)))=
    oldSignedCellAverage Q depth (fun U => ∑ i,
      (oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k (F i) (hF i))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k (G i) (hG i))-
      volumeAverage (openCubeSet U.val) (fun x => vecDot (F i x).2 (G i x).2))) := by
  simp_rw [old_signed_mixed_pairing_partition Q depth nu sigma hnu hsigma k _ _ (hF _) (hG _)]
  rw [old_signed_cell_average_sum]

end
end ASDExplicitGamma.Native

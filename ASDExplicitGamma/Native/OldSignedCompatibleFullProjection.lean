module

public import ASDExplicitGamma.Native.OldSignedCompatibleFullMean
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans

/-! Full-block projection control for a genuine compatible field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Exact full-block projection energy as an average of physical means. -/
theorem old_signed_full_projection_energy_eq_means (Q : TriadicCube 2) (j : ℕ)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    (∑ i,energy Q (cubeProjection Q j (fun x => (F x).1 i)))+
      (∑ i,energy Q (cubeProjection Q j (fun x => (F x).2 i)))=
        descendantsAverage Q j (fun U => blockVecDot (oldSignedBlockMean U F) (oldSignedBlockMean U F)) := by
  rw [vector_projection_energy_eq_means Q j (fun x => (F x).1)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i)),
    vector_projection_energy_eq_means Q j (fun x => (F x).2)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))]
  rw [←descendantsAverage_add]
  rfl

/-- Both projected components are paid by the same full-response depth
maximum and actual physical energy, without a spurious dimension factor. -/
theorem old_signed_compatible_full_projection_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → BlockVec 2}
    (hF : ScalarCompatible (openCubeSet Q) F) :
    (∑ i,energy Q (cubeProjection Q depth (fun x => (F x).1 i)))+
      (∑ i,energy Q (cubeProjection Q depth (fun x => (F x).2 i))) ≤
    fullResponseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) depth*
      oldSignedEnergyPairing Q nu sigma k F F := by
  rw [old_signed_full_projection_energy_eq_means Q depth F hF.1,
    old_signed_energy_pairing_partition Q depth nu sigma hnu hsigma k hF.1 hF.1,
    ←old_signed_cell_average_mul,
    ←old_signed_cell_average_eq_descendantsAverage Q depth
      (fun U => blockVecDot (oldSignedBlockMean U F) (oldSignedBlockMean U F))]
  apply old_signed_cell_average_mono
  intro U
  let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hU k
  have h := old_signed_compatible_full_mean_bound U.val nu sigma hnu hsigma kU
    (old_signed_compatible_restrict Q U.val hU hF)
  have heq : fullResponseOperatorNorm U.val (responseFramePlanarCoefficientField nu sigma kU)=
      fullResponseOperatorNorm U.val (responseFramePlanarCoefficientField nu sigma k) := by
    unfold fullResponseOperatorNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U.val,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U.val,
      old_signed_cell_coarse_matrix_eq Q U.val hU nu sigma k]
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (full_response_norm_le_depth_max Q U.val (responseFramePlanarCoefficientField nu sigma k) depth U.property)
    (old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma kU F))

end
end ASDExplicitGamma.Native

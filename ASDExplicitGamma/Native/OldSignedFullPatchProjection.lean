module

public import ASDExplicitGamma.Native.OldSignedCompatibleFullProjection
public import ASDExplicitGamma.Native.OldSignedPatchProjection

/-! Full-block affine patch projection and its exact compatible energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The actual affine patch has its full prescribed mean on each child. -/
theorem old_signed_patch_block_mean (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    oldSignedBlockMean U (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P))=P := by
  have hae := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P) U hU
  rw [old_signed_affine_cell_residual] at hae
  have he : oldSignedBlockMean U (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P))=
      oldSignedBlockMean U (oldSignedFrameCanonicalField U nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k) P) := by
    apply Prod.ext <;> funext i
    all_goals
      simp only [oldSignedBlockMean,cubeAverage_eq_integralAverage_openCubeSet,integralAverage]
      congr 1
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
  rw [he,old_signed_canonical_block_mean]

/-- Full physical means subtract linearly on genuine square-integrable fields. -/
theorem old_signed_block_mean_sub (Q : TriadicCube 2) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedBlockMean Q (F-G)=oldSignedBlockMean Q F-oldSignedBlockMean Q G := by
  apply Prod.ext <;> funext i
  · exact old_signed_cube_average_sub Q
      (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i))
      (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hG) i))
  · exact old_signed_cube_average_sub Q
      (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
      (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hG) i))

/-- Full-block projections of a compatible field minus affine data are
controlled by the exact difference from the genuine child minimizer patch. -/
theorem old_signed_full_patch_projection_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (S : Vec 2 → BlockVec 2) (hS : ScalarCompatible (openCubeSet Q) S) :
    let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    (∑ i,energy Q (cubeProjection Q depth (fun x => (S x).1 i-P.1 i)))+
      (∑ i,energy Q (cubeProjection Q depth (fun x => (S x).2 i-P.2 i))) ≤
    fullResponseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) depth*
      oldSignedEnergyPairing Q nu sigma k (S-L) (S-L) := by
  intro L
  have hL := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  have hh := old_signed_compatible_full_projection_bound Q depth nu sigma hnu hsigma k
    (old_signed_compatible_sub hS (old_signed_patch_compatible Q depth nu sigma hnu hsigma k P))
  rw [old_signed_full_projection_energy_eq_means Q depth (S-L) (hS.1.sub hL)] at hh
  have he : (∑ i,energy Q (cubeProjection Q depth (fun x => (S x).1 i-P.1 i)))+
      (∑ i,energy Q (cubeProjection Q depth (fun x => (S x).2 i-P.2 i)))=
      descendantsAverage Q depth (fun U => blockVecDot (oldSignedBlockMean U (S-L)) (oldSignedBlockMean U (S-L))) := by
    have hproj := old_signed_full_projection_energy_eq_means Q depth (S-(fun _ => P))
      (hS.1.sub (memLp_const P))
    simp only [Pi.sub_apply,Prod.fst_sub,Prod.snd_sub] at hproj
    rw [hproj]
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    have hsU := hS.1.mono_measure (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    have hlU := hL.mono_measure (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    rw [old_signed_block_mean_sub U hsU (memLp_const P),old_signed_block_mean_sub U hsU hlU,
      old_signed_patch_block_mean Q depth nu sigma hnu hsigma k P U hU]
    simp only [oldSignedBlockMean,cubeAverage_const]
  rw [he]
  exact hh

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedAffineCellResidual
public import ASDExplicitGamma.Native.OldSignedCanonicalFullMean
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans

/-! Affine means and compatibility of the actual finite child patch. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The child affine patch has its prescribed first mean on each child. -/
theorem old_signed_patch_first_mean (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (i : Fin 2) :
    cubeAverage U (fun x => (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P) x).1 i)=P.1 i := by
  have hae := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P) U hU
  rw [old_signed_affine_cell_residual] at hae
  have he : cubeAverage U (fun x => (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P) x).1 i)=
      (oldSignedBlockMean U (oldSignedFrameCanonicalField U nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k) P)).1 i := by
    simp only [oldSignedBlockMean,cubeAverage_eq_integralAverage_openCubeSet,integralAverage]
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    exact congrArg (fun z : BlockVec 2 => z.1 i) hx
  rw [he,old_signed_canonical_block_mean]

/-- Constant affine data are compatible in the physical parent square. -/
theorem old_signed_constant_compatible (Q : TriadicCube 2) (P : BlockVec 2) :
    ScalarCompatible (openCubeSet Q) (fun _ => P) := by
  have hdom := (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
  have hvol : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  exact ⟨memLp_const P,(H1Function.affineOnIsSobolevRegularDomain hdom P.1).isPotentialOn,
    IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain hdom hvol P.2⟩

/-- The finite affine patch is globally compatible; only its removed
correction, not the parent's cell restriction, has zero boundary traces. -/
theorem old_signed_patch_compatible (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ScalarCompatible (openCubeSet Q) (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)) := by
  have hh := old_signed_compatible_sub (old_signed_constant_compatible Q P)
    (scalar_variation_compatible (old_signed_local_removed_variation Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)))
  have he : ((fun _ : Vec 2 => P)-(fun x => P-oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P) x))=oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P) := by
    funext x
    simp only [Pi.sub_apply,sub_sub_cancel]
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native

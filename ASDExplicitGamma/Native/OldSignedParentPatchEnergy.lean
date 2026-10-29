module

public import ASDExplicitGamma.Native.OldSignedAffineCellResidual
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing

/-! The exact ordinary parent-versus-patch energy gap, with the actual
parent field and actual child affine minimizers kept distinct. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar
noncomputable section

/-- The difference between the genuine parent affine minimizer and the
patch of genuine child affine minimizers is a parent variation. -/
theorem old_signed_parent_patch_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q)
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)) := by
  have hp := old_signed_canonical_error_variation Q
    (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) P
  have hc := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  have hh := scalar_variation_add hp hc
  have he : ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P))=
      (fun x => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-P)+
      (fun x => P-oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x) := by
    funext x
    simp only [Pi.sub_apply,Pi.add_apply]
    abel
  rw [he]
  exact hh

/-- The exact energy of the actual patched child affine minimizers is the
physical average of their coarse quadratic forms. -/
theorem old_signed_affine_patch_energy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    oldSignedEnergyPairing Q nu sigma k R R=descendantsAverage Q depth (fun U =>
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k)) P)) := by
  intro R
  dsimp only [R]
  rw [old_signed_local_residual_cell_pairing]
  simp_rw [old_signed_affine_cell_energy]
  exact old_signed_cell_average_eq_descendantsAverage Q depth (fun U =>
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (responseFramePlanarCoefficientField nu sigma k)) P))

/-- Exact ordinary patch energy, retaining the favorable negative parent
term. It holds for every doubled affine load, hence both canonical pairs. -/
theorem old_signed_parent_patch_energy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedEnergyPairing Q nu sigma k (S-R) (S-R)=
      descendantsAverage Q depth (fun U => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P))-
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
  intro S R a
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hR := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  have ho := old_signed_canonical_variation_pairing Q nu sigma hnu hsigma k P
    (old_signed_parent_patch_variation Q depth nu sigma hnu hsigma k P)
  change oldSignedEnergyPairing Q nu sigma k S (S-R)=0 at ho
  rw [old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hS hS hR] at ho
  have he : oldSignedEnergyPairing Q nu sigma k (S-R) (S-R)=
      oldSignedEnergyPairing Q nu sigma k R R-oldSignedEnergyPairing Q nu sigma k S S := by
    rw [old_signed_energy_pairing_sub_left Q nu sigma hnu hsigma k hS hR (hS.sub hR),
      old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hS hS hR,
      old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hR hS hR,
      old_signed_energy_pairing_symm Q nu sigma k R S]
    linarith only [ho]
  rw [he,old_signed_affine_patch_energy,old_signed_canonical_energy]

end
end ASDExplicitGamma.Native

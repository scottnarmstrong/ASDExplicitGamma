module

public import ASDExplicitGamma.Native.OldSignedComplementaryPairing

/-! The complementary patch energy in its compatible reciprocal form,
ready for the actual depth-projection estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar
noncomputable section

/-- Dual reflection is self-adjoint for the physical energy pairing. -/
theorem old_signed_dual_reflection_self_adjoint (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k (oldSignedDualReflection Q nu sigma k F) G=
      oldSignedEnergyPairing Q nu sigma k F (oldSignedDualReflection Q nu sigma k G) := by
  rw [old_signed_energy_pairing_symm Q nu sigma k (oldSignedDualReflection Q nu sigma k F) G,
    old_signed_dual_reflection_pairing Q nu sigma hnu hsigma k,
    old_signed_dual_reflection_pairing Q nu sigma hnu hsigma k]
  congr 1
  funext x
  simp only [blockVecDot,Prod.swap]
  rw [vecDot_comm (G x).1,vecDot_comm (G x).2]
  ring

/-- The reciprocal-compatible comparison has the exact positive companion
energy, including its affine cross; no trace surplus is discarded. -/
theorem old_signed_reciprocal_patch_energy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) :
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => W) (memLp_const W)
    let JS := oldSignedDualReflection Q nu sigma k S
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedEnergyPairing Q nu sigma k (JS-R) (JS-R)=
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P)+
      descendantsAverage Q depth (fun U => blockVecDot W
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) W))-2*blockVecDot P W.swap := by
  intro S R JS a
  have hR := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => W) (memLp_const W)
  have hJS := old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (F := S) (Lp.memLp _)
  have hcross : oldSignedEnergyPairing Q nu sigma k JS R=blockVecDot P W.swap := by
    rw [old_signed_dual_reflection_self_adjoint Q nu sigma hnu hsigma k]
    exact old_signed_parent_reflected_patch_pairing Q depth nu sigma hnu hsigma k P W
  rw [old_signed_energy_pairing_sub_left Q nu sigma hnu hsigma k hJS hR (hJS.sub hR),
    old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hJS hJS hR,
    old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hR hJS hR,
    old_signed_energy_pairing_symm Q nu sigma k R JS,hcross,
    old_signed_dual_reflection_isometry Q nu sigma hnu hsigma k,
    old_signed_canonical_energy,old_signed_affine_patch_energy]
  ring

end
end ASDExplicitGamma.Native

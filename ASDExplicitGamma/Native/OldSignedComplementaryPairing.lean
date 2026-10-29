module

public import ASDExplicitGamma.Native.OldSignedDualReflection
public import ASDExplicitGamma.Native.OldSignedCanonicalFullMean
public import ASDExplicitGamma.Native.OldSignedParentPatchEnergy

/-! Exact complementary cross pairing for the actual parent and affine
child patch, using only the global parent mean and genuine Hodge tests. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The actual reflection is linear under subtraction of physical fields. -/
theorem old_signed_dual_reflection_sub (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2) :
    oldSignedDualReflection Q nu sigma k (F-G)=
      oldSignedDualReflection Q nu sigma k F-oldSignedDualReflection Q nu sigma k G := by
  funext x
  simp only [oldSignedDualReflection,Pi.sub_apply,sub_eq_add_neg]
  rw [blockMatVecMul_add, show -G x = (-1 : ℝ) • G x by simp, blockMatVecMul_smul]
  simp only [neg_one_smul]
  rfl

/-- Compatible fields annihilate reflected zero-trace variations in the
actual energy pairing. This is the physical complementary Hodge identity. -/
theorem old_signed_compatible_reflected_variation_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {F Y : Vec 2 → BlockVec 2} (hF : ScalarCompatible (openCubeSet Q) F)
    (hY : ScalarVariation (openCubeSet Q) Y) :
    oldSignedEnergyPairing Q nu sigma k F (oldSignedDualReflection Q nu sigma k Y)=0 := by
  rw [old_signed_dual_reflection_pairing Q nu sigma hnu hsigma k]
  have he : (fun x => blockVecDot (F x) (Y x).swap)=
      (fun x => blockVecDot (scalarBlockExchange (F x)) (Y x)) := by
    funext x
    simp only [blockVecDot,Prod.swap,scalarBlockExchange]
    ring
  rw [he]
  unfold volumeAverage
  rw [scalar_compatible_exchange_pairing_zero hF hY,mul_zero]

/-- The canonical reflected constant test uses the exact full parent
mean, with no cell-boundary hypothesis on the parent field. -/
theorem old_signed_canonical_reflected_constant_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (oldSignedDualReflection Q nu sigma k (fun _ => W))=blockVecDot P W.swap := by
  rw [old_signed_dual_reflection_pairing Q nu sigma hnu hsigma k]
  have hh := old_signed_constant_block_pairing_mean Q
    (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) W.swap
  rw [old_signed_canonical_block_mean] at hh
  simpa only [blockVecDot_comm] using hh

/-- The complementary parent/patch cross is exactly the pairing of the
two affine loads, after the genuine patch correction is annihilated. -/
theorem old_signed_parent_reflected_patch_pairing (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P W : BlockVec 2) :
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => W) (memLp_const W)
    oldSignedEnergyPairing Q nu sigma k S (oldSignedDualReflection Q nu sigma k R)=blockVecDot P W.swap := by
  intro S R
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hR : MemBlockL2 (openCubeSet Q) R := old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => W) (memLp_const W)
  have ho := old_signed_compatible_reflected_variation_pairing Q nu sigma hnu hsigma k
    (F := S) (Y := (fun _ => W)-R)
    (old_signed_canonical_compatible Q nu sigma hnu hsigma k P)
    (old_signed_local_removed_variation Q depth nu sigma hnu hsigma k (fun _ => W) (memLp_const W))
  change oldSignedEnergyPairing Q nu sigma k S
    (oldSignedDualReflection Q nu sigma k ((fun _ => W)-R))=0 at ho
  rw [old_signed_dual_reflection_sub,old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hS
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (memLp_const W))
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k hR)] at ho
  exact (sub_eq_zero.mp ho).symm.trans
    (old_signed_canonical_reflected_constant_pairing Q nu sigma hnu hsigma k P W)

end
end ASDExplicitGamma.Native

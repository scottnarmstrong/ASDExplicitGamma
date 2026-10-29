module

public import ASDExplicitGamma.Native.OldSignedDirectionalDepthMatrix
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans

/-! Positivity of the exact coarse directional majorant from the two
physical comparison energies, rather than a sign premise on an inverse trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- Physical ellipticity makes every actual self-pairing nonnegative. -/
theorem old_signed_energy_pairing_nonneg (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) : 0 ≤ oldSignedEnergyPairing Q nu sigma k F F :=
  compatible_blockPairingAverage_nonneg
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) ⟨fun x => (F x).1,fun x => (F x).2⟩

/-- The majorant is nonnegative in every physical load direction, as the
sum of the ordinary and complementary comparison energies. -/
theorem old_signed_paired_depth_quadratic_nonneg (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    0 ≤ vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth
      (responseFramePlanarCoefficientField nu sigma k)) e) := by
  let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,e)
  let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => (0,e)) (memLp_const (0,e))
  let T := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => (e,0)) (memLp_const (e,0))
  have hh := add_nonneg (old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k (S-R))
    (old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k (oldSignedDualReflection Q nu sigma k S-T))
  dsimp only [S,R,T] at hh
  rw [old_signed_parent_patch_energy,old_signed_reciprocal_patch_energy] at hh
  have he :
      (descendantsAverage Q depth (fun U => blockVecDot (0,e)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k)) (0,e))))+
      (descendantsAverage Q depth (fun U => blockVecDot (e,0)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k)) (e,0))))-
      2*blockVecDot (0,e) (e,0).swap=
        vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth (responseFramePlanarCoefficientField nu sigma k)) e) := by
    rw [← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,
      ← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,old_signed_paired_matrix_quadratic]
    rfl
  rw [←he]
  linarith only [hh]

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.OldSignedCoarsePairing
public import ASDExplicitGamma.Scalar.ProjectionFields

/-! The reciprocal gradient mean is the physical coarse block. This keeps
AN (6.3) signed even when the expected bottom block is below the identity. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
noncomputable section

/-- The plain representative of the actual affine Hilbert minimizer. -/
def oldSignedCanonicalAffineField (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    BlockL2 (openCubeSet Q) :=
  hilbertBlockL2ToBlockL2 ((scalarCellSystem Q a hEll).toMuHilbertRealization.minimizerMap P)

/-- Physical constant tests of the actual minimizer recover the full coarse
block form, not an assumed matrix representation. -/
theorem old_signed_affine_field_constant_test (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P R : BlockVec 2) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot R
      (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x))) =
    blockVecDot R (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
  let S := oldSignedCanonicalAffineField Q a hEll P
  have hc : toHilbertBlockL2OfBlockField (U := openCubeSet Q) (F := fun _ => R) (memLp_const R) =
      blockVecToHilbertBlockL2Const R := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := openCubeSet Q) (memLp_const R),
      coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) R] with x hx hy
    exact hx.trans hy.symm
  have hb := (scalarCellSystem Q a hEll).toMuOperatorRealization.energyBilin_eq_volumeAverage_swap_of_memBlockL2
      (show MemBlockL2 (openCubeSet Q) (fun _ => R) from memLp_const R) (Lp.memLp S)
  rw [hc] at hb
  dsimp only [S,oldSignedCanonicalAffineField] at hb
  rw [hilbert_field_rebuild] at hb
  exact hb.symm.trans (old_signed_canonical_constant_pairing Q a hEll P R)

/-- Each actual reciprocal-gradient coordinate is integrable before its
mean or a signed covariance series is used. -/
theorem old_signed_reciprocal_coordinate_integrable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) (i : Fin 2) :
    IntegrableOn (fun x =>
      (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x)).2 i)
      (openCubeSet Q) := by
  let X : BlockState 2 := ⟨fun _ => 0,fun _ => basisVec i⟩
  let Y : BlockState 2 := ⟨fun x => (oldSignedCanonicalAffineField Q a hEll P x).1,
    fun x => (oldSignedCanonicalAffineField Q a hEll P x).2⟩
  have h := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    (X := X) (Y := Y) (show MemBlockL2 (openCubeSet Q) X.eval from memLp_const (0,basisVec i))
    (show MemBlockL2 (openCubeSet Q) Y.eval from Lp.memLp _) hEll
  change IntegrableOn (fun x => blockVecDot (0,basisVec i)
    (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x)))
    (openCubeSet Q) at h
  simpa only [blockVecDot,vecDot_zero_left,zero_add,vecDot_basisVec_left] using h

/-- Every reciprocal-gradient coordinate has the exact mean specified by the
coarse matrix, with the molecular coefficient inside a and no positivity
assumption on a partially inserted law's expected block. -/
theorem old_signed_reciprocal_mean_coordinate (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) (i : Fin 2) :
    volumeAverage (openCubeSet Q) (fun x =>
      (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x)).2 i) =
    (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P).2 i := by
  have h := old_signed_affine_field_constant_test Q a hEll P (0,basisVec i)
  simpa only [blockVecDot,vecDot_zero_left,zero_add,vecDot_basisVec_left] using h

/-- For a bottom affine load, the reciprocal mean recovers the actual lower
right coarse matrix entry. -/
theorem old_signed_bottom_block_mean (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i j : Fin 2) :
    volumeAverage (openCubeSet Q) (fun x =>
      (blockMatVecMul (blockCoeffField a x)
        (oldSignedCanonicalAffineField Q a hEll (0,basisVec j) x)).2 i) =
    (coarseBlockMatrix (openCubeSet Q) a).lowerRight i j := by
  have h := old_signed_reciprocal_mean_coordinate Q a hEll (0,basisVec j) i
  fin_cases j <;> simpa [blockMatVecMul_snd,matVecMul_zero,matVecMul,basisVec,Matrix.mulVec, dotProduct,Pi.single_apply] using h

end
end ASDExplicitGamma.Native

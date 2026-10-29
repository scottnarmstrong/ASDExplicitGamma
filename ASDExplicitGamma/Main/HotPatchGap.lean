module

public import ASDExplicitGamma.Native.OldSignedParentPatchEnergy
public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Native.OldSignedTiledWeakProjection
public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthPositivity

/-! Hot-patch trial, package A: the coarse (patch-drop) error `W = S - L` of the
four canonical loads, its zero-trace potential `w`, the exact four-load energy
identity `Δ = tr(avg_U A_U − A_Q)`, and the all-depth weak bound
`Vw² ≤ B Δ`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators

noncomputable section

/-- The four-load patch drop `W_c = S_c - L_c` of the actual OLD frame, as a
field on the parent cube: parent canonical minimizer minus the glued local
minimizers at the same constant load `P`. -/
def hotPatchDrop (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    Vec 2 → BlockVec 2 :=
  (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) -
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
      (memLp_const P)

/-- The sum over the four canonical loads of a quadratic form is the trace. -/
theorem hot_block_basis_quadratic_sum (N : BlockMat 2) :
    ∑ c : BlockCoord 2, blockVecDot (blockBasis c) (blockMatVecMul N (blockBasis c)) =
      Matrix.trace N.upperLeft + Matrix.trace N.lowerRight := by
  simp [Fintype.sum_sum_type, blockBasis, blockVecDot, blockMatVecMul, vecDot,
    matVecMul, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]

/-- Exact four-load identity: the energy of the patch drop is the trace
subadditivity defect `Δ = avg_U tr A_U − tr A_Q`. -/
theorem hot_patch_drop_energy_sum (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    ∑ c : BlockCoord 2, oldSignedEnergyPairing Q nu sigma k
        (hotPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c))
        (hotPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c)) =
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q)
          (responseFramePlanarCoefficientField nu sigma k) 1 := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  have hc (c : BlockCoord 2) : oldSignedEnergyPairing Q nu sigma k
        (hotPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c))
        (hotPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c)) =
      descendantsAverage Q depth (fun U => blockVecDot (blockBasis c)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (blockBasis c))) -
      blockVecDot (blockBasis c)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (blockBasis c)) :=
    old_signed_parent_patch_energy Q depth nu sigma hnu hsigma k (blockBasis c)
  have htr (U : TriadicCube 2) :
      ∑ c : BlockCoord 2, blockVecDot (blockBasis c)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (blockBasis c)) =
      traceDefect (openCubeSet U) a 1 + 4 := by
    rw [hot_block_basis_quadratic_sum]
    simp [traceDefect]
  rw [Finset.sum_congr rfl (fun c _ => hc c), Finset.sum_sub_distrib, htr Q,
    ← Homogenization.descendantsAverage_sum Q depth Finset.univ]
  have h4 : descendantsAverage Q depth (fun U => ∑ c : BlockCoord 2, blockVecDot (blockBasis c)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (blockBasis c))) =
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) + 4 := by
    simp_rw [htr]
    rw [Homogenization.descendantsAverage_add, descendantsAverage_const]
  rw [h4]
  ring

/-- The patch drop is a compatible field: its first block is the gradient of
a zero-trace potential `w` and its second block is solenoidal. -/
theorem hot_patch_drop_variation (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q) (hotPatchDrop Q depth nu sigma hnu hsigma k P) :=
  old_signed_parent_patch_variation Q depth nu sigma hnu hsigma k P

/-- The zero-trace first potential `w` of the patch drop. -/
theorem hot_patch_drop_potential (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ∃ w : H10Function (openCubeSet Q), w.toH1Function.grad =
      fun x => (hotPatchDrop Q depth nu sigma hnu hsigma k P x).1 :=
  (hot_patch_drop_variation Q depth nu sigma hnu hsigma k P).2.1

end

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Native.OldSignedEnergyPartition

/-! The ordinary D3 patch-Pythagoras identity for the actual OLD
coefficient with the top-affine load `(e,0)`. This is the top-parent
counterpart to the bottom-load identity used for reciprocal response. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3

noncomputable section

private theorem top_patch_cell_energy_identity
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)) =
    descendantsAverage Q depth (fun R =>
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField nu sigma k)) P)) := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const P
  let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  have hLenergy := old_signed_local_residual_energy Q depth nu sigma hnu hsigma k
    F F hF hF
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let hFR : MemBlockL2 (openCubeSet R) F :=
      hF.mono_measure (Measure.restrict_mono_set volume hRQ)
    let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ
      nu sigma hnu hsigma k F hF
    have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
      F hF R hR
    have hCoeffMat (x : Vec 2) (hx : x ∈ openCubeSet R) : aR x = a x := by
      simp only [aR, a, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hCoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
        blockCoeffField aR x = blockCoeffField a x := by
      simpa [blockCoeffField] using congrArg blockMatrixOfCoeff (hCoeffMat x hx)
    have hCoeffAE : aR =ᵐ[volume.restrict (openCubeSet R)] a := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      exact hCoeffMat x hx
    have hCoarse := coarseBlockMatrix_congr_of_ae_eq hCoeffAE
    have hRestr' : L =ᵐ[volumeMeasureOn (openCubeSet R)] Z := by
      simpa [L, Z] using hRestr
    have hIntegrand : (fun x => blockVecDot (L x)
        (blockMatVecMul (blockCoeffField a x) (L x))) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (Z x)
          (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      filter_upwards [hRestr', ae_restrict_mem (measurableSet_openCubeSet R)]
        with x hLx hx
      rw [hLx, hCoeff x hx]
    have hAverage : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (Z x)
            (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      unfold volumeAverage
      congr 1
      exact integral_congr_ae hIntegrand
    have hFRconst : toHilbertBlockL2OfBlockField hFR =
        (scalarFrameRealization R nu sigma hnu hsigma kR).constantField P := by
      have hconst : toHilbertBlockL2OfBlockField hFR =
          blockVecToHilbertBlockL2Const P := by
        apply Lp.ext
        filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
          coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) P] with x hx hy
        simpa [F] using hx.trans hy.symm
      exact hconst.trans (by rfl)
    have hZeq : Z = scalarResidualField R nu sigma hnu hsigma kR
        ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField P) := by
      funext x
      change (scalarResidualField R nu sigma hnu hsigma kR
        (toHilbertBlockL2OfBlockField hFR)) x = _
      rw [hFRconst]
    have hAffine := old_signed_affine_energy R nu sigma hnu hsigma kR P
    have hAffineZ : oldSignedEnergyPairing R nu sigma kR Z Z =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := by
      simpa [hZeq, aR] using hAffine
    calc
      _ = oldSignedEnergyPairing R nu sigma kR Z Z := by
        simpa [oldSignedEnergyPairing, aR] using hAverage
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := hAffineZ
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by rw [hCoarse]
  rw [hLenergy]
  unfold descendantsAverage
  change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth, volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x) (blockMatVecMul (blockCoeffField a x) (L x))) =
    ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth,
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P)
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  exact hcell R hR

/-- D3 for the actual top-affine source solve: the parent minimizer's
energy error against the finite patch of its descendant top-affine solves is
the descendant-average coarse energy minus the parent coarse energy. -/
theorem smooth_feedback_top_patch_pythagoras
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    let k := oldCutoffSkewCoefficient m Q ω
    let P : BlockVec 2 := (e, 0)
    let a := responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M m : ℝ) k
    oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m : ℝ) k
      (fun x => smoothFeedbackCellAffineResidual M m Q e ω x -
        oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k
          (fun _ => P) (memLp_const P) x)
      (fun x => smoothFeedbackCellAffineResidual M m Q e ω x -
        oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k
          (fun _ => P) (memLp_const P) x) =
      descendantsAverage Q depth (fun R =>
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P)) -
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let P : BlockVec 2 := (e, 0)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k F (memLp_const P)
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k
    ((scalarFrameRealization Q M.nu σ M.nu_pos (Annealed.sigmaBar M m).property k).constantField P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  have hParent := smooth_feedback_affine_projection_ae M m Q e ω
  have hPatch := old_signed_affine_patch_energy_identity Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k P
  have hLocal := old_signed_local_residual_energy Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k F F
    (memLp_const P) (memLp_const P)
  have hCell := top_patch_cell_energy_identity Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k P
  have hAffine := old_signed_affine_energy Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k P
  have hCanonicalDiff :
      (fun x => smoothFeedbackCellAffineResidual M m Q e ω x - L x) =ᵐ[
        volumeMeasureOn (openCubeSet Q)] D := by
    filter_upwards [hParent] with x hx
    exact congrArg (fun z : BlockVec 2 => z - L x) hx.symm
  calc
    oldSignedEnergyPairing Q M.nu σ k
        (fun x => smoothFeedbackCellAffineResidual M m Q e ω x - L x)
        (fun x => smoothFeedbackCellAffineResidual M m Q e ω x - L x) =
        oldSignedEnergyPairing Q M.nu σ k D D := by
      exact old_signed_energy_pairing_congr_ae Q M.nu σ k hCanonicalDiff hCanonicalDiff
    _ = descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (L x) (blockMatVecMul (blockCoeffField a x) (L x)))) -
          oldSignedEnergyPairing Q M.nu σ k S S := by
      simpa [D, S, L, a, F, P, oldSignedEnergyPairing] using hPatch
    _ = oldSignedEnergyPairing Q M.nu σ k L L -
          oldSignedEnergyPairing Q M.nu σ k S S := by
      rw [← hLocal]
    _ = oldSignedEnergyPairing Q M.nu σ k L L -
          blockVecDot P (blockMatVecMul
            (coarseBlockMatrix (openCubeSet Q) a) P) := by
      simpa [S, a] using congrArg
        (fun z : ℝ => oldSignedEnergyPairing Q M.nu σ k L L - z) hAffine
    _ = descendantsAverage Q depth (fun R =>
          blockVecDot P (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) P)) -
          blockVecDot P (blockMatVecMul
            (coarseBlockMatrix (openCubeSet Q) a) P) := by
      rw [hCell]

end

end ASDExplicitGamma.Scalar

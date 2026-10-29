module

public import ASDExplicitGamma.Main.HotPatchGap
public import ASDExplicitGamma.Scalar.OldHessianTrialCellBudget

/-! MA-E-COVARIANCE, step 1: the paired two-potential Bessel bound for the hot
patch drop `W = S - L` on the depth-`depth` source tiling.  On each source cell
`W` is a homogeneous response (parent minus cell minimizer), so one paired
Bessel budget pays the first block and the reciprocal block together. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Response Scalar Triadic Variational
open ASDExplicitGamma.Native
open scoped BigOperators

noncomputable section

/-- The cell comparison `W_{c,U} = S|_U - L_U` of the parent canonical
minimizer and the cell minimizer at the constant load `P`. -/
def hotCovCmp (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d)
    (P : BlockVec 2) : BlockState 2 :=
  oldHessianParentCellComparison Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k P

/-- The reciprocal block `g_W` of the cell comparison, in the parent physical
coefficient. -/
def hotCovCmpRecip (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d)
    (P : BlockVec 2) : Vec 2 → Vec 2 := fun x =>
  (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
    ((hotCovCmp Q d nu sigma hnu hsigma k U P).eval x)).2

/-- Paired weak bound of the hot patch drop over the whole source tiling: the
first and reciprocal blocks of all four loads share one history budget `B` and
the single trace-subadditivity defect. -/
theorem hot_cov_paired_drop_weak (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (B : ℝ)
    (hB : ∀ U ∈ descendantsAtDepth Q d,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
      vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential +
      vectorWeakHaarEnergy U.val
        (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) ≤
      B * (descendantsAverage Q d (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1) := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hcell (c : BlockCoord 2) (U : OldSignedCellIndex Q d) :
      vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential +
      vectorWeakHaarEnergy U.val
        (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c)) ≤
      B * blockPairingAverage (openCubeSet U.val) a
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c))
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)) := by
    have h := old_hessian_parent_cell_paired_weak Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
      (blockBasis c)
    dsimp only at h
    refine h.trans (mul_le_mul_of_nonneg_right (hB U.val U.property) ?_)
    exact compatible_blockPairingAverage_nonneg
      (hEll.mono (measurableSet_openCubeSet U.val)
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)) _
  have hsum : ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
      vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential +
      vectorWeakHaarEnergy U.val
        (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) ≤
      ∑ c : BlockCoord 2, B * oldSignedCellAverage Q d (fun U =>
        blockPairingAverage (openCubeSet U.val) a
          (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c))
          (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c))) := by
    apply Finset.sum_le_sum
    intro c _
    rw [← old_signed_cell_average_mul]
    exact old_signed_cell_average_mono Q d (fun U => hcell c U)
  refine hsum.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← hot_patch_drop_energy_sum Q d nu sigma hnu hsigma k]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  have hp := old_hessian_patch_drop_parent_partition Q d nu sigma hnu hsigma k
    (blockBasis c)
  unfold oldHessianPatchDrop at hp
  exact hp.symm

end

end ASDExplicitGamma.Main

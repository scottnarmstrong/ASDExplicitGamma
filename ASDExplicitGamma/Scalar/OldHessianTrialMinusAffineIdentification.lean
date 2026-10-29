module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatGlobalTriangle
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineEnergy

/-! Exact identification of the original minus affine family after spatial averaging. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- An original minus cell mean is literally pure first. -/
theorem old_hessian_minus_mean_pure_first (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (p : whiteBasisIndex×Fin 2) :
    oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L p.1 p.2)=
      ((oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L p.1 p.2)).1,0) := by
  simp [oldSignedFlatMinusBlock,oldSignedBlockMean,cubeAverage_const]
  rfl

/-- The spatial full-block affine family is exactly the complete original
minus top-energy family, after justified cell/mode interchange. -/
theorem old_hessian_actual_minus_affine_identification (M : ABKModel 2) (m : ℤ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U =>
      oldHessianFlatAffineCellEnergy (originCube 2 (m+129)) U.val
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient (m+129) m ω)) b L false)=oldHessianMinusAffineEnergy M m b L ω := by
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let q := oldHessianMinusMeanColumn Q 134 b L
  let f := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134) =>
    vecDot (q p U) (matVecMul (coarseBlockMatrix (openCubeSet U.val) a).upperLeft (q p U))
  have he (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134) :
      (let v := oldSignedBlockMean U.val (oldSignedFlatInput Q b L false p.1 p.2)
       blockVecDot v (blockMatVecMul (coarseBlockMatrix (openCubeSet U.val) a) v))=f p U := by
    change blockVecDot (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L p.1 p.2))
      (blockMatVecMul (coarseBlockMatrix (openCubeSet U.val) a)
        (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L p.1 p.2)))=_
    rw [old_hessian_minus_mean_pure_first]
    simp only [blockVecDot,blockMatVecMul,matVecMul_zero,add_zero,vecDot_zero_left]
    rfl
  have hn (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134) : 0≤f p U := by
    rw [←he]
    have hh := old_hessian_affine_quadratic_nonneg U.val M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedBlockMean U.val (oldSignedFlatInput Q b L false p.1 p.2))
    rw [old_signed_cell_coarse_matrix_eq] at hh
    exact hh
  have hs (U : OldSignedCellIndex Q 134) : Summable (fun p => f p U) := by
    have hh := old_hessian_flat_affine_cell_series Q 134 a b L false U
    have hh' : Summable (fun n => ∑ i : Fin 2,f (n,i) U) :=
      hh.congr (fun n => Finset.sum_congr rfl (fun i _ => he (n,i) U))
    exact (summable_prod_of_nonneg (fun p => hn p U)).2
      ⟨fun _ => Summable.of_finite,by simpa only [tsum_fintype] using hh'⟩
  have hcell (U : OldSignedCellIndex Q 134) : oldHessianFlatAffineCellEnergy Q U.val a b L false=∑' p,f p U := by
    rw [(hs U).tsum_prod]
    simp only [tsum_fintype,oldHessianFlatAffineCellEnergy]
    apply tsum_congr
    intro n
    exact Finset.sum_congr rfl (fun i _ => he (n,i) U)
  change oldSignedCellAverage Q 134 (fun U => oldHessianFlatAffineCellEnergy Q U.val a b L false)=_
  simp_rw [hcell]
  exact (old_signed_cell_average_series Q 134 f hs).2.symm

end
end ASDExplicitGamma.Scalar

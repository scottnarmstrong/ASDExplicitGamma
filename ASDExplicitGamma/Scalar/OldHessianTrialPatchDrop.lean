module

public import ASDExplicitGamma.Native.OldSignedPhysicalFluxTrace
public import ASDExplicitGamma.Variational.Subadditivity
public import ASDExplicitGamma.Cold.CoarseGramDefect

/-! Exact coarse/fine patch budgets for the signed principal covariance.
The coarse bottom and fine top gaps share one complete fine trace payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Variational
noncomputable section

/-- Actual energy of the parent-minus-affine-patch comparison. -/
def oldHessianPatchDrop (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) : ℝ :=
  let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
  oldSignedEnergyPairing Q nu sigma k (S-L) (S-L)

theorem old_hessian_patch_drop_nonneg (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    0≤oldHessianPatchDrop Q depth nu sigma hnu hsigma k P :=
  old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k _

/-- The exact identity retains the negative parent energy. -/
theorem old_hessian_patch_drop_eq (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldHessianPatchDrop Q depth nu sigma hnu hsigma k P =
      descendantsAverage Q depth (fun U => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P))-
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) :=
  old_signed_parent_patch_energy Q depth nu sigma hnu hsigma k P

/-- Successive refinements increase the actual directional patch quadratic
form on the same coefficient; no comparison of unrelated matrix caps is used. -/
theorem old_hessian_patch_quadratic_monotone (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    Monotone (fun depth => descendantsAverage Q depth (fun U =>
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P))) := by
  apply monotone_nat_of_le_succ
  intro depth
  rw [descendantsAverage_succ_eq_descendantsAverage_descendantsAverage]
  apply descendantsAverage_le_descendantsAverage
  intro U hU
  have hh := cube_coarse_matrix_subadditive U 1 a
    (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)) P
  rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat] at hh
  linarith only [hh]

/-- The coarse comparison drop is bounded by the fine drop for every load. -/
theorem old_hessian_patch_drop_mono (Q : TriadicCube 2) (coarse fine : ℕ)
    (hdepth : coarse≤fine) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldHessianPatchDrop Q coarse nu sigma hnu hsigma k P ≤
      oldHessianPatchDrop Q fine nu sigma hnu hsigma k P := by
  rw [old_hessian_patch_drop_eq,old_hessian_patch_drop_eq]
  exact sub_le_sub_right (old_hessian_patch_quadratic_monotone Q _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) P hdepth) _

/-- Summing the four genuine patch drops gives exactly the full trace gap. -/
theorem old_hessian_full_patch_trace_identity (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ c : BlockCoord 2,oldHessianPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c)) =
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1)-
        traceDefect (openCubeSet Q) a 1 := by
  intro a
  simp_rw [old_hessian_patch_drop_eq]
  rw [Finset.sum_sub_distrib,←Homogenization.descendantsAverage_sum]
  simp_rw [old_signed_coarse_basis_trace_sum]
  simp only [traceDefect,inv_one,one_mul]
  rw [old_signed_descendants_average_sub,descendantsAverage_const]
  ring

/-- The coarse bottom and fine top drops are paid by the one complete fine
trace. This is the signed covariance budget: the fine a5 is retained. -/
theorem old_hessian_mixed_patch_trace_bound (Q : TriadicCube 2) (coarse fine : ℕ)
    (hdepth : coarse≤fine) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ i : Fin 2,oldHessianPatchDrop Q coarse nu sigma hnu hsigma k (0,basisVec i))+
      (∑ i : Fin 2,oldHessianPatchDrop Q fine nu sigma hnu hsigma k (basisVec i,0)) ≤
        descendantsAverage Q fine (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_hessian_patch_drop_mono Q coarse fine hdepth nu sigma hnu hsigma k (0,basisVec i))
  have he := old_hessian_full_patch_trace_identity Q fine nu sigma hnu hsigma k
  rw [Fintype.sum_sum_type] at he
  have hr := Cold.coarse_square_traceDefect_nonneg Q
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k)
  change _ ≤ descendantsAverage Q fine (fun U => traceDefect (openCubeSet U) a 1)
  change (∑ i : Fin 2,oldHessianPatchDrop Q fine nu sigma hnu hsigma k (basisVec i,0))+
    (∑ i : Fin 2,oldHessianPatchDrop Q fine nu sigma hnu hsigma k (0,basisVec i)) =
      descendantsAverage Q fine (fun U => traceDefect (openCubeSet U) a 1)-
        traceDefect (openCubeSet Q) a 1 at he
  linarith only [hm,he,hr]

/-- In particular, the actual coarse two-bottom-load drop is bounded by its
own completed r4 trace, with no extra load-count factor. -/
theorem old_hessian_bottom_patch_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ i : Fin 2,oldHessianPatchDrop Q depth nu sigma hnu hsigma k (0,basisVec i)) ≤
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have hh := old_hessian_mixed_patch_trace_bound Q depth depth le_rfl nu sigma hnu hsigma k
  have ht := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    old_hessian_patch_drop_nonneg Q depth nu sigma hnu hsigma k (basisVec i,0))
  linarith only [hh,ht]

end
end ASDExplicitGamma.Scalar

module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatCellTriangleSeries
public import ASDExplicitGamma.Native.OldSignedFlatPatchedData
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Spatial affine/centered triangle for the original complete flat projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Complete affine energy of the original flat means on one cell. -/
def oldHessianFlatAffineCellEnergy (Q U : TriadicCube 2) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  ∑' n : whiteBasisIndex,∑ i : Fin 2,
    let m := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
    blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) m)

/-- Complete affine mode convergence follows from the actual flat mean
square series, with no positivity of a signed identity deviation assumed. -/
theorem old_hessian_flat_affine_cell_series (Q : TriadicCube 2) (fine : ℕ)
    (a : CoeffField 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : OldSignedCellIndex Q fine) :
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,
      let m := oldSignedBlockMean U.val (oldSignedFlatInput Q b L plus n i)
      blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U.val) a) m)) := by
  apply summable_sum
  intro i _
  let m := fun n => oldSignedBlockMean U.val (oldSignedFlatInput Q b L plus n i)
  have hs : Summable (fun n => blockVecDot (m n) (m n)) := by
    cases plus
    · exact old_signed_flat_minus_mean_series Q fine b L i U.val U.property
    · exact old_signed_flat_plus_mean_series Q fine b L i U.val U.property
  have hh := (old_signed_affine_deviation_summable (coarseBlockMatrix (openCubeSet U.val) a) m hs).add hs
  simpa only [sub_add_cancel] using hh

/-- The full original flat energy has the constant-one spatial triangle.
Both full mode convergence and the actual affine/oscillatory factors are retained. -/
theorem old_hessian_flat_global_triangle (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := fun n i => oldSignedPatchedFlat Q fine nu sigma hnu hsigma k b L plus n i
    let E := fun n => ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k (Z n i) (Z n i)
    let P := oldSignedCellAverage Q fine (fun U => oldHessianFlatAffineCellEnergy Q U.val a b L plus)
    let O := oldSignedCellAverage Q fine (fun U => oldSignedResponseHistory U.val a*oldSignedFlatOscillationSize Q U.val b L plus^2)
    Summable E ∧ (∑' n,E n)≤P+2*(Real.sqrt P*Real.sqrt O)+O := by
  intro a Z E P O
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q fine) =>
    let Z := fun i => oldSignedFlatCellResidual Q fine nu sigma hnu hsigma k b L plus n i U.val U.property
    ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (Z i) (Z i)
  let pc := fun U : OldSignedCellIndex Q fine => oldHessianFlatAffineCellEnergy Q U.val a b L plus
  let oc := fun U : OldSignedCellIndex Q fine => oldSignedResponseHistory U.val a*oldSignedFlatOscillationSize Q U.val b L plus^2
  have hp (U : OldSignedCellIndex Q fine) : 0≤pc U := by
    apply tsum_nonneg
    intro n
    apply Finset.sum_nonneg
    intro i _
    have hh := old_hessian_affine_quadratic_nonneg U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedBlockMean U.val (oldSignedFlatInput Q b L plus n i))
    rw [old_signed_cell_coarse_matrix_eq] at hh
    exact hh
  have ho U : 0≤oc U := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hcell (U : OldSignedCellIndex Q fine) := old_hessian_actual_flat_cell_triangle_series Q fine
    nu sigma hnu hsigma k b L plus U.val U.property
  have hb (U : OldSignedCellIndex Q fine) : (∑' n,fc n U)≤pc U+2*(Real.sqrt (pc U)*Real.sqrt (oc U))+oc U := by
    have he : Real.sqrt (oc U)=Real.sqrt (oldSignedResponseHistory U.val a)*oldSignedFlatOscillationSize Q U.val b L plus := by
      have hM : 0≤oldSignedResponseHistory U.val a := ENNReal.toReal_nonneg
      have hO : 0≤oldSignedFlatOscillationSize Q U.val b L plus := Real.sqrt_nonneg _
      dsimp only [oc]
      rw [Real.sqrt_mul hM,Real.sqrt_sq hO]
    rw [he]
    exact (hcell U).2.trans_eq (by dsimp only [pc,oc,oldHessianFlatAffineCellEnergy]; ring)
  have hh := old_signed_cell_average_series_upper Q fine fc _ (fun U => (hcell U).1) hb
  have he : E=(fun n => oldSignedCellAverage Q fine (fc n)) := by
    funext n
    change (∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k _ _)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k _ _))=_
    simp_rw [old_signed_local_residual_cell_pairing]
    rw [old_signed_cell_average_sum]
    rfl
  rw [he]
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [old_signed_cell_average_add,old_signed_cell_average_add,old_signed_cell_average_mul]
  have hc := old_signed_cell_average_root_cauchy Q fine pc oc hp ho
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤2))) le_rfl

end
end ASDExplicitGamma.Scalar

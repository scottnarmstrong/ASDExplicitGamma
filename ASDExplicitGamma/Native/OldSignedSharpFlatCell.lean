module

public import ASDExplicitGamma.Native.OldSignedSharpPureFlat
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds

/-! Sharp physical-flux affine energy on the actual flat source cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Triadic
noncomputable section

/-- The actual flat-cell energy estimate has no regularity or estimated
projection premise. The coarse matrix and histories belong to the parent medium. -/
theorem old_signed_actual_flat_cell_energy_sharp (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let F := oldSignedFlatInput Q b L plus n i
    let Z := oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U hU
    let m := oldSignedBlockMean U F
    let O := oldSignedBlockPositiveNorm U (F-fun _ => m)
    oldSignedEnergyPairing U nu sigma kU Z Z ≤
      blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) m)+
      2*Real.sqrt (2*oldSignedCorrectorHistory U a)*Real.sqrt (blockVecDot m m)*O+
      oldSignedResponseHistory U a*O^2 := by
  intro a kU F Z m O
  let e : Vec 2 := if plus then m.2 else m.1
  have hm : m=oldSignedDirectionalLoad plus e := by
    cases plus <;> simp [m,F,e,oldSignedFlatInput,oldSignedFlatPlusBlock,oldSignedFlatMinusBlock,
      oldSignedBlockMean,oldSignedDirectionalLoad,cubeAverage_const]
    all_goals rfl
  have hnorm : vecNormSq e=blockVecDot m m := by
    rw [hm]
    cases plus <;> simp [oldSignedDirectionalLoad,blockVecDot,vecNormSq,vecDot]
  have hh := old_signed_flat_projection_energy_pure_mean U nu sigma hnu hsigma kU F
    (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU) plus e hm
    (old_signed_flat_input_cell_first_positive Q depth b L plus n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L plus n i U hU m.2)
  dsimp only at hh
  rw [hnorm] at hh
  have hc := old_signed_cell_coarse_matrix_eq Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma k
  have hs := old_signed_cell_histories Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
  rw [hc,hs.2.1,hs.2.2] at hh
  simpa only [Z,oldSignedFlatCellResidual,F,kU,O,m,a,Pi.sub_def,mul_assoc] using hh


end
end ASDExplicitGamma.Native

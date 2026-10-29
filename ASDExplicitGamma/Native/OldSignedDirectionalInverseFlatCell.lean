module

public import ASDExplicitGamma.Native.OldSignedPureSecondInverseFlatEnergy
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds

/-! The literal plus flat source consumes the paired directional proxy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Triadic
noncomputable section

/-- Actual plus-cell energy, with its directional reciprocal cross and no
regularity or estimated affine-flux premise. -/
theorem old_signed_actual_plus_cell_energy_directional_inverse (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let F := oldSignedFlatInput Q b L true n i
    let Z := oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L true n i U hU
    let m := oldSignedBlockMean U F
    let O := oldSignedBlockPositiveNorm U (F-fun _ => m)
    oldSignedEnergyPairing U nu sigma kU Z Z ≤
      blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) m)+
      2*Real.sqrt (oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField nu sigma kU) m.2)*O+
      oldSignedInverseHistory U a*O^2 := by
  intro a kU F Z m O
  have hm : m=(0,m.2) := by
    simp [m,F,oldSignedFlatInput,oldSignedFlatPlusBlock,oldSignedBlockMean,cubeAverage_const]
    rfl
  have hz (x : Vec 2) : (F x).1=0 := rfl
  have hh := old_signed_flat_projection_energy_pure_second_inverse U nu sigma hnu hsigma kU F
    (old_signed_flat_input_cell_memL2 Q depth b L true n i U hU) m.2 hz hm
    (old_signed_flat_input_cell_first_positive Q depth b L true n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L true n i U hU m.2)
  dsimp only at hh
  have hc := old_signed_cell_coarse_matrix_eq Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma k
  have hs := old_signed_cell_histories Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
  rw [hc,hs.1] at hh
  simpa only [Z,oldSignedFlatCellResidual,F,kU,O,m,a,Pi.sub_def,mul_assoc] using hh

end
end ASDExplicitGamma.Native

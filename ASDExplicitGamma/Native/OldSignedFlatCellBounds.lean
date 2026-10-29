module

public import ASDExplicitGamma.Native.OldSignedFlatCellRegularity
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedFlatBounds

/-! Actual flat inputs discharge the regularity hypotheses of the cell
projection bounds. Every history is that of the same parent coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual weighted child projection of either physical flat input. -/
def oldSignedFlatCellResidual (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) : Vec 2 → BlockVec 2 :=
  scalarResidualField U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)
    (toHilbertBlockL2OfBlockField (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU))

/-- The actual flat-cell energy estimate has no regularity or estimated
projection premise. The coarse matrix and histories belong to the parent medium. -/
theorem old_signed_actual_flat_cell_energy (Q : TriadicCube 2) (depth : ℕ)
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
      2*Real.sqrt (6*oldSignedCorrectorHistory U a)*Real.sqrt (blockVecDot m m)*O+
      oldSignedResponseHistory U a*O^2 := by
  intro a kU F Z m O
  have hh := old_signed_flat_projection_energy U nu sigma hnu hsigma kU F
    (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU)
    (old_signed_flat_input_cell_first_positive Q depth b L plus n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L plus n i U hU m.2)
  change oldSignedEnergyPairing U nu sigma kU Z Z ≤
    blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (responseFramePlanarCoefficientField nu sigma kU)) m)+
    2*Real.sqrt (6*oldSignedCorrectorHistory U (responseFramePlanarCoefficientField nu sigma kU))*
      Real.sqrt (blockVecDot m m)*O+
    oldSignedResponseHistory U (responseFramePlanarCoefficientField nu sigma kU)*O^2 at hh
  have hc := old_signed_cell_coarse_matrix_eq Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma k
  have hs := old_signed_cell_histories Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
  rw [hc,hs.2.1,hs.2.2] at hh
  exact hh

/-- The actual reciprocal projection error obeys the sharp affine and
oscillation estimate, with every source regularity premise discharged. -/
theorem old_signed_actual_flat_cell_reciprocal (Q : TriadicCube 2) (depth : ℕ)
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
    vectorWeakHaarNorm U (fun x =>
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (Z x)).2-(F x).2) ≤
      Real.sqrt (6*oldSignedCorrectorHistory U a)*Real.sqrt (blockVecDot m m)+
        (oldSignedResponseHistory U a+1)*O := by
  intro a kU F Z m O
  have hh := old_signed_flat_reciprocal_weak U nu sigma hnu hsigma kU F
    (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU)
    (old_signed_flat_input_cell_first_positive Q depth b L plus n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L plus n i U hU m.2)
  have hs := old_signed_cell_histories Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
  dsimp only at hh
  rw [hs.2.1,hs.2.2] at hh
  exact hh

end
end ASDExplicitGamma.Native

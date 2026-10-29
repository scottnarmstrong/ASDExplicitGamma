module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatEnergyTriangle
public import ASDExplicitGamma.Native.OldSignedSharpFlatCellSeries

/-! The unchanged actual flat cell projection with its full affine energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A literal coarse affine energy is nonnegative for every block load. -/
theorem old_hessian_affine_quadratic_nonneg (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    0≤blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField nu sigma k)) P) := by
  rw [←old_signed_affine_energy Q nu sigma hnu hsigma k P,
    ←old_signed_energy_inner_fields Q nu sigma hnu hsigma k (Lp.memLp _) (Lp.memLp _)]
  exact real_inner_self_nonneg

/-- Actual flat cell energy retains its whole affine energy in the cross,
so its annealed payment uses (1+a5/2) rather than an extra trace-history factor. -/
theorem old_hessian_actual_flat_cell_triangle (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let Z := oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U hU
    let m := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
    let P := blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) m)
    let O := oldSignedBlockPositiveNorm U (oldSignedFlatInput Q b L plus n i-fun _ => m)
    oldSignedEnergyPairing U nu sigma kU Z Z≤P+
      (2*Real.sqrt (oldSignedResponseHistory U a))*(Real.sqrt P*O)+oldSignedResponseHistory U a*O^2 := by
  intro a kU Z m P O
  have hh := old_hessian_flat_projection_energy_triangle U nu sigma hnu hsigma kU
    (oldSignedFlatInput Q b L plus n i) (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU)
    (old_signed_flat_input_cell_first_positive Q depth b L plus n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L plus n i U hU m.2)
  have hc := old_signed_cell_coarse_matrix_eq Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma k
  have hs := old_signed_cell_histories Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
  dsimp only at hh
  rw [hc,hs.2.1] at hh
  have hP : 0≤P := by
    have hp := old_hessian_affine_quadratic_nonneg U nu sigma hnu hsigma kU m
    rw [hc] at hp
    exact hp
  have hM : 0≤oldSignedResponseHistory U a := ENNReal.toReal_nonneg
  have he : (Real.sqrt P+Real.sqrt (oldSignedResponseHistory U a)*O)^2=
      P+(2*Real.sqrt (oldSignedResponseHistory U a))*(Real.sqrt P*O)+oldSignedResponseHistory U a*O^2 := by
    nlinarith only [Real.sq_sqrt hP,congrArg (fun z : ℝ => z*O^2) (Real.sq_sqrt hM)]
  have hh' : oldSignedEnergyPairing U nu sigma kU Z Z≤
      (Real.sqrt P+Real.sqrt (oldSignedResponseHistory U a)*O)^2 := by
    simpa only [Z,oldSignedFlatCellResidual,kU,a,P,O,m,Pi.sub_def] using hh
  exact hh'.trans_eq he

end
end ASDExplicitGamma.Scalar

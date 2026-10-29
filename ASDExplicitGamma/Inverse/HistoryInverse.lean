module

public import ASDExplicitGamma.Inverse.HistoryResponse
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! Actual coarse inverse bounds in the one completed true frame, as inputs
to the complete inverse-lambda history comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational
noncomputable section

/-- The actual pure-flux block cap, with the completed label's true frame. -/
theorem actual_framed_lower_right_norm_le_defect (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (Annealed.sigmaBar M n:ℝ)*Book.Ch02.matrixNorm
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun).lowerRight ≤
        2*(1+historyOperatorDefect M n Q ω) := by
  let σ := (Annealed.sigmaBar M n:ℝ)
  let A := coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun
  let C := frameMatrix σ A
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  have hC : IsSymmetricBlockMat C := history_frame_symmetric σ A (history_coarse_symmetric Q _ hEll)
  have hpos (P : BlockVec 2) : 0 ≤ blockVecDot P (blockMatVecMul C P) := by
    have hh := clipped_source_quadratic_nonneg M n Q ω (toFullBlockVec P)
    change 0 ≤ fullMatrixQuadratic (toFullBlockVec P) (toFullBlockMat C) at hh
    rwa [fullMatrixQuadratic_block] at hh
  have hc := positive_lower_right_norm_le C hC hpos
  have hdef : 0 ≤ historyOperatorDefect M n Q ω := norm_nonneg _
  have hb := (clipped_source_norm_le_of_defect M n Q ω _ hdef le_rfl).trans
    (response_envelope_le_linear _ hdef)
  have he : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C.lowerRight‖=
      σ*Book.Ch02.matrixNorm A.lowerRight := by
    change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (σ • A.lowerRight)‖=_
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
    rfl
  rw [he] at hc
  exact hc.trans hb

/-- The genuine sigmaStarInv inverse response has that same exact Euclidean
meaning; no molecular frame is substituted. -/
theorem actual_inverse_response_le_defect (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (Annealed.sigmaBar M n:ℝ)*Book.Ch02.matrixNorm
      (sigmaStarInvCoarse (openCubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun) ≤
        2*(1+historyOperatorDefect M n Q ω) := by
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  rw [ASDExplicitGamma.Scalar.inverse_history_lowerRight Q _
    (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))]
  exact actual_framed_lower_right_norm_le_defect M n Q ω

end
end ASDExplicitGamma.Inverse

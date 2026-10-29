module

public import ASDExplicitGamma.Inverse.ClippedMatrixResponseQuadratic
public import ASDExplicitGamma.Inverse.ClippedMatrixSymmetricNorm
public import ASDExplicitGamma.Inverse.ClippedMatrixSource

/-! Sharp Euclidean operator response cap from the variational pair inequalities. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- Source bound for a symmetric doubled matrix with the true pairing
lower bounds. Its only norm input is the reflected defect. -/
theorem clipped_block_response_norm_bound (C : BlockMat 2) (hC : IsSymmetricBlockMat C)
    (hp : ∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (hn : ∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (t : ℝ) (ht : 0 ≤ t)
    (hH : ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (historyDefectMatrix C)‖ ≤ t) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat C)‖ ≤
      1+t+Real.sqrt (t*(t+2)) := by
  have hHerm : (toFullBlockMat C).IsHermitian := by
    simpa [Matrix.IsHermitian,Matrix.IsSymm] using isSymm_toFullBlockMat_of_isSymmetricBlockMat hC
  have he (v : FullBlockVec 2) : dotProduct v ((toFullBlockMat C).mulVec v) =
      blockVecDot (ofFullBlockVec v) (blockMatVecMul C (ofFullBlockVec v)) := by
    change fullMatrixQuadratic v (toFullBlockMat C) = _
    simpa only [toFullBlockVec_ofFullBlockVec] using fullMatrixQuadratic_block C (ofFullBlockVec v)
  apply clipped_symmetric_norm_le_of_quadratic _ hHerm _ (by positivity)
  · intro v
    rw [he]
    have hp' := hp (ofFullBlockVec v).1 (ofFullBlockVec v).2
    have hn' := hn (ofFullBlockVec v).1 (ofFullBlockVec v).2
    linarith only [hp',hn']
  · intro v
    rw [he]
    have hh := clipped_block_response_quadratic_bound C hp hn t ht hH (ofFullBlockVec v)
    have hv : dotProduct v v=blockVecDot (ofFullBlockVec v) (ofFullBlockVec v) := by
      simpa only [toFullBlockVec_ofFullBlockVec] using
        dotProduct_toFullBlockVec (ofFullBlockVec v) (ofFullBlockVec v)
    simpa only [hv] using hh

/-- The actual completed coefficient has the sharp source response cap
whenever its same-frame reflected operator defect is at most t. -/
theorem clipped_source_norm_le_of_defect (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (t : ℝ) (ht : 0 ≤ t) (hH : historyOperatorDefect M n Q ω ≤ t) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (clippedSourceMatrix M n Q ω)‖ ≤
      1+t+Real.sqrt (t*(t+2)) := by
  obtain ⟨Lam,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M n ω Q
  have hp := history_framed_pair_bounds Q _ M.nu_pos hEll _ (Annealed.sigmaBar_characterization M n).1
  exact clipped_block_response_norm_bound _
    (history_frame_symmetric _ _ (history_coarse_symmetric Q _ hEll)) hp.1 hp.2 t ht hH

end
end ASDExplicitGamma.Inverse

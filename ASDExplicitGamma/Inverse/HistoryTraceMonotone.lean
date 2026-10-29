module

public import ASDExplicitGamma.Inverse.HistoryBuffer
public import ASDExplicitGamma.Variational.Subadditivity

/-! Subadditivity makes the depth maxima nondecreasing in the fixed cutoff and frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- Positive diagonal weights take a block Loewner inequality to a trace inequality. -/
theorem history_weighted_trace_mono (A B : BlockMat 2) (sigma : ℝ) (hs : 0 < sigma)
    (h : BlockMatLoewnerLE A B) :
    sigma⁻¹*Matrix.trace A.upperLeft+sigma*Matrix.trace A.lowerRight-4 ≤
      sigma⁻¹*Matrix.trace B.upperLeft+sigma*Matrix.trace B.lowerRight-4 := by
  have h0 := h (blockBasis (Sum.inl 0))
  have h1 := h (blockBasis (Sum.inl 1))
  have h2 := h (blockBasis (Sum.inr 0))
  have h3 := h (blockBasis (Sum.inr 1))
  simp only [blockBasis_pairing,blockMatEntry] at h0 h1 h2 h3
  have hUL : Matrix.trace A.upperLeft ≤ Matrix.trace B.upperLeft := by
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
    linarith only [h0,h1]
  have hLR : Matrix.trace A.lowerRight ≤ Matrix.trace B.lowerRight := by
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
    linarith only [h2,h3]
  have ha := mul_le_mul_of_nonneg_left hUL (inv_nonneg.mpr hs.le)
  have hb := mul_le_mul_of_nonneg_left hLR hs.le
  linarith only [ha,hb]

theorem history_trace_subadditive (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    historyTrace M n Q ω ≤ descendantsAverage Q j (fun R => historyTrace M n R ω) := by
  have h := history_weighted_trace_mono _ _ _ (Annealed.sigmaBar_characterization M n).1
    (Variational.cutoff_coarse_matrix_subadditive M n Q j ω)
  have he : descendantsAverage Q j (fun R => historyTrace M n R ω) =
      (Annealed.sigmaBar M n : ℝ)⁻¹*Matrix.trace
        (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu n ω).toFun)).upperLeft+
      (Annealed.sigmaBar M n : ℝ)*Matrix.trace
        (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight-4 := by
    simp only [historyTrace,traceDefect,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
    dsimp only [descendantsAverageBlockMat,descendantsAverageMat]
    simp only [sub_eq_add_neg,descendantsAverage_add,descendantsAverage_mul_left,descendantsAverage_const]
  rw [he]
  exact h

end ASDExplicitGamma.Inverse

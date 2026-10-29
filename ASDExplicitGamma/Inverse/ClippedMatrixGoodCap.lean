module

public import ASDExplicitGamma.Inverse.ClippedMatrixResponseBound
public import ASDExplicitGamma.Inverse.ClippedMatrixEvent

/-! Actual good-history clipping has the sharp source cap g(tau). -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The depth-zero term of the literal raw history contains the current cell. -/
theorem clipped_operator_defect_le_raw_history (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (historyOperatorDefect M n Q ω) ≤ clippedCellRawHistory M n Q ω := by
  have hh := ENNReal.le_tsum (f := fun r : ℕ =>
    ENNReal.ofReal ((3:ℝ)^(-(1/2:ℝ)*r))*historyFiniteMax (descendantsAtDepth Q r)
      (fun R ω => ENNReal.ofReal (historyOperatorDefect M n R ω)) ω) 0
  simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero,ENNReal.ofReal_one,one_mul,
    descendantsAtDepth_zero,historyFiniteMax,Finset.sup_singleton,clippedCellRawHistory] using hh

/-- Actual history-good event implies the same cell's defect cap. -/
theorem clipped_operator_defect_le_of_good (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    historyOperatorDefect M n Q ω ≤ τ :=
  (ENNReal.ofReal_le_ofReal_iff hτ).mp ((clipped_operator_defect_le_raw_history M n Q ω).trans hgood)

/-- Sharp g(tau) cap for the actual clipped matrix; no moment or response
bound is assumed, and the constant is independent of nu. -/
theorem clipped_cell_matrix_norm_le (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (clippedCellMatrix M n Q τ ω)‖ ≤
      1+τ+Real.sqrt (τ*(τ+2)) := by
  by_cases hg : ω ∈ clippedCellGoodEvent M n Q τ
  · have he : clippedCellMatrix M n Q τ ω=clippedSourceMatrix M n Q ω := Set.indicator_of_mem hg _
    rw [he]
    exact clipped_source_norm_le_of_defect M n Q ω τ hτ (clipped_operator_defect_le_of_good M n Q τ hτ ω hg)
  · have he : clippedCellMatrix M n Q τ ω=0 := Set.indicator_of_notMem hg _
    rw [he,map_zero,norm_zero]
    positivity

end
end ASDExplicitGamma.Inverse

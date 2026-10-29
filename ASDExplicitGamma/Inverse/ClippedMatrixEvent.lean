module

public import ASDExplicitGamma.Inverse.ClippedMatrixMean

/-! The actual unnormalized good-history event in the clipped source matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal

private instance clippedMatrixESeminormedAddMonoid : ESeminormedAddMonoid (FullBlockMat 2) := by
  change ESeminormedAddMonoid (BlockCoord 2 → BlockCoord 2 → ℝ)
  infer_instance

/-- Literal raw history, at an arbitrary physical cell, with a fixed completed
cutoff and that label's true frame in every descendant. -/
noncomputable def clippedCellRawHistory (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ∑' r : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * r)) *
    historyFiniteMax (descendantsAtDepth Q r)
      (fun R ω => ENNReal.ofReal (historyOperatorDefect M n R ω)) ω

/-- Measurability includes the full infinite history and every finite descendant maximum. -/
theorem clipped_cell_raw_history_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Measurable (clippedCellRawHistory M n Q) :=
  Measurable.tsum (fun _r => (history_finite_max_measurable _ _
    (fun R => (history_operator_defect_measurable M n R).ennreal_ofReal)).const_mul _)

/-- The source good event D_j^40(Q)<=tau, with n=j+40. -/
def clippedCellGoodEvent (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ) :
    Set (Cutoff.CutoffSample 2) := {ω | clippedCellRawHistory M n Q ω ≤ ENNReal.ofReal tau}

/-- The actual good-history event is measurable. -/
theorem clipped_cell_good_event_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ) :
    MeasurableSet (clippedCellGoodEvent M n Q tau) :=
  measurableSet_le (clipped_cell_raw_history_measurable M n Q) measurable_const

/-- Literal full 4x4 matrix of the source event; no cluster mask is included. -/
noncomputable def clippedCellMatrix (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ) :
    Cutoff.CutoffSample 2 → FullBlockMat 2 :=
  (clippedCellGoodEvent M n Q tau).indicator (clippedSourceMatrix M n Q)

/-- The full old-history clipping has its genuine matrix-valued integrable mean. -/
theorem clipped_cell_matrix_integrable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (tau : ℝ) :
    Integrable (clippedCellMatrix M n Q tau) (Cutoff.cutoffSampleLaw M).toMeasure := by
  change Integrable ((clippedCellGoodEvent M n Q tau).indicator (clippedSourceMatrix M n Q))
    (Cutoff.cutoffSampleLaw M).toMeasure
  exact Integrable.indicator (ε' := FullBlockMat 2) (f := clippedSourceMatrix M n Q)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (clipped_source_integrable M n Q)
    (clipped_cell_good_event_measurable M n Q tau)

/-- The source full-matrix mean cap follows from the protected ordinary buffer
mean in the same frame. It applies to every load, including both blocks. -/
theorem clipped_cell_matrix_mean_le (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n - 40) (hg : 0 < M.gamma) (hgmax : M.gamma ≤ gammaZero)
    (hbuf : bufferMean M n ≤ ENNReal.ofReal (8 / 25 * theta M)) (tau : ℝ)
    (v : BlockCoord 2 → ℝ) :
    fullMatrixQuadratic v (∫ ω, clippedCellMatrix M n Q tau ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (29 / 25 : ℝ) * dotProduct v v :=
  clipped_source_mean_le M n Q hQ hg hgmax hbuf _ (clipped_cell_good_event_measurable M n Q tau) v

end ASDExplicitGamma.Inverse

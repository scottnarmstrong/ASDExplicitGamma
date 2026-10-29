module

public import ASDExplicitGamma.Inverse.FullResponseShearedLayerMean

/-! Positivity of the exactly sheared clipped matrix and its full layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational

noncomputable section

/-- Arbitrary actual load transformations preserve clipped trace positivity. -/
theorem clipped_congruence_normalized_trace_nonneg
    (M : ABKModel 2) (n : ℤ) (P : TriadicCube 2) (τ : ℝ)
    (ω : Cutoff.CutoffSample 2) (R : FullBlockMat 2) :
    0 ≤ Matrix.trace (R.transpose*clippedCellMatrix M n P τ ω*R)/4 := by
  have hdiag (i : BlockCoord 2) :
      0 ≤ (R.transpose*clippedCellMatrix M n P τ ω*R) i i := by
    have hh := clipped_cell_matrix_quadratic_nonneg M n P τ ω (R.mulVec (Pi.single i 1))
    rw [← fullMatrixQuadratic_congruence] at hh
    change 0 ≤ dotProduct (Pi.single i 1)
      ((R.transpose*clippedCellMatrix M n P τ ω*R).mulVec (Pi.single i 1)) at hh
    simpa only [single_dotProduct, one_mul,
      Matrix.mulVec_single_one, Matrix.col_apply] using hh
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => hdiag i

/-- Each complete exactly sheared full-response layer is nonnegative,
before any mask is removed or any conditioning is used. -/
theorem full_response_sheared_layer_trace_nonneg
    (M : ABKModel 2) (Q : TriadicCube 2) (H i : ℕ) (N : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseShearedLayerTrace M Q H i N weights ω := by
  unfold fullResponseShearedLayerTrace
  apply Finset.sum_nonneg
  intro U hU
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (clipped_congruence_normalized_trace_nonneg M (U.scale+40) U
      (rootTau .full) ω _)

end
end ASDExplicitGamma.Inverse

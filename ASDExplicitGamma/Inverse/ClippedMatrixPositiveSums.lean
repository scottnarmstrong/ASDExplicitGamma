module

public import ASDExplicitGamma.Inverse.ClippedMatrixConditional

/-! Positivity permits geometry-selected subsets to be enlarged before conditioning. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal

/-- The literal clipped source matrix is positive in all load directions. -/
theorem clipped_cell_matrix_quadratic_nonneg (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (tau : ℝ) (ω : Cutoff.CutoffSample 2) (v : BlockCoord 2 → ℝ) :
    0 ≤ fullMatrixQuadratic v (clippedCellMatrix M n Q tau ω) := by
  change 0 ≤ fullMatrixQuadratic v ((clippedCellGoodEvent M n Q tau).indicator
    (clippedSourceMatrix M n Q) ω)
  by_cases hω : ω ∈ clippedCellGoodEvent M n Q tau
  · rw [Set.indicator_of_mem hω]
    exact clipped_source_quadratic_nonneg M n Q ω v
  · rw [Set.indicator_of_notMem hω]
    exact le_of_eq (fullMatrixQuadratic v).map_zero.symm

end ASDExplicitGamma.Inverse

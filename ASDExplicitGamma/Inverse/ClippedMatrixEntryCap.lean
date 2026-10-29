module

public import ASDExplicitGamma.Inverse.ClippedMatrixGoodCap

/-! Actual clipped matrix entries inherit the sharp Euclidean cap. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- Each scalar entry is bounded by the genuine Euclidean operator norm. -/
theorem clipped_matrix_entry_abs_le_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) :
    |A i j| ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ := by
  let x : EuclideanSpace ℝ n := PiLp.single 2 j 1
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have he : (T x) i=A i j := by
    simp [T,x,Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct]
  calc
    |A i j| = ‖(T x) i‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ‖T x‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖*‖x‖ := T.le_opNorm x
    _ = ‖T‖ := by simp [x,PiLp.norm_single]

/-- Complete actual entry bound for the clipped matrix, with no boundedness
hypothesis supplied by a concentration consumer. -/
theorem clipped_cell_matrix_entry_abs_le (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) (i j : BlockCoord 2) :
    |clippedCellMatrix M n Q τ ω i j| ≤ 1+τ+Real.sqrt (τ*(τ+2)) :=
  (clipped_matrix_entry_abs_le_norm _ i j).trans (clipped_cell_matrix_norm_le M n Q τ hτ ω)

end
end ASDExplicitGamma.Inverse

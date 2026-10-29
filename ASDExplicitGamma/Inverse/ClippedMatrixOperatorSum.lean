module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.Basis

/-! Explicit Euclidean operator norm payment by scalar entries. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- One matrix entry has Euclidean operator norm at most its absolute value. -/
theorem clipped_matrix_single_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (a : ℝ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.single i j a)‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro x
  have he : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.single i j a) x =
      PiLp.single 2 i (a*x j) := by
    ext k
    by_cases hk : k=i
    · subst k
      simp [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct,Matrix.single]
    · simp [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct,Matrix.single,hk,Ne.symm hk]
  rw [he,PiLp.norm_single,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg a)

/-- The literal Euclidean operator norm is bounded by the sum of absolute
entries; no entrywise norm is used as an operator norm. -/
theorem clipped_matrix_operator_norm_le_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ ≤ ∑ i, ∑ j, |A i j| := by
  have he : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A =
      ∑ i, ∑ j, Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Matrix.single i j (A i j)) := by
    calc
      _ = Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (∑ i, ∑ j, Matrix.single i j (A i j)) :=
        congrArg (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (Matrix.matrix_eq_sum_single A)
      _ = _ := by simp only [map_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun j _ => clipped_matrix_single_norm_le i j (A i j))

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Cold.GramOperator
public import ASDExplicitGamma.Cold.SpectralPair
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # The sharp Gram coefficient for a genuine positive response matrix -/

@[expose] public section
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The Euclidean operator norm of the actual symmetrized response defect. -/
def matrixGramDefect {n : Type*} [Fintype n] [DecidableEq n] (A R : Matrix n n ℝ) : ℝ :=
  ‖gramSymmetrizedDefect ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n)) A) ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n)) R)‖

/-- Symmetry and the literal involution identity imply Euclidean norm preservation. -/
theorem matrix_reflection_norm {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (hR : R.IsHermitian) (hRR : R * R = 1)
    (x : EuclideanSpace ℝ n) : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := n)) R x‖ = ‖x‖ := by
  have hrr : R.toEuclideanLin (R.toEuclideanLin x) = x := by
    have h := congrArg (fun B : Matrix n n ℝ => B.toEuclideanLin x) hRR
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
      LinearMap.comp_apply, LinearMap.id_apply] using h
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hR
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  change ⟪R.toEuclideanLin x,R.toEuclideanLin x⟫ = ⟪x,x⟫
  rw [hs, hrr]

end ASDExplicitGamma.Cold

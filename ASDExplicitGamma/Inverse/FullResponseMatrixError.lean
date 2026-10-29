module

public import ASDExplicitGamma.Inverse.ClippedMatrixQuadratic
public import ASDExplicitGamma.Inverse.ClippedMatrixSource
public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! Full-load quadratic errors are controlled by the Euclidean operator norm
of the same genuine doubled matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory
open ASDExplicitGamma.Variational
open scoped Matrix.Norms.Elementwise

/-- Every full paired loading tests a matrix perturbation by at most its
Euclidean operator norm times the squared loading norm. -/
theorem full_matrix_quadratic_abs_le_euclidean_opNorm
    (A : FullBlockMat 2) (v : BlockCoord 2 → ℝ) :
    |fullMatrixQuadratic v A| ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ * dotProduct v v := by
  let x : EuclideanSpace ℝ (BlockCoord 2) := WithLp.toLp 2 v
  have hnormSq : ‖x‖ ^ 2 = dotProduct v v := by
    calc
      ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
      _ = dotProduct v v := by
        simp [x, dotProduct, Real.norm_eq_abs, sq_abs]
        ring
  have hinner : inner ℝ x ((Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A) x) =
      fullMatrixQuadratic v A := by
    simpa [x, fullMatrixQuadratic] using Matrix.inner_toEuclideanCLM A x x
  calc
    |fullMatrixQuadratic v A| = |inner ℝ x
        ((Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A) x)| :=
      congrArg abs hinner.symm
    _ ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A) x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg x)
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ * dotProduct v v := by
      rw [← hnormSq]
      ring

/-- The normalized full trace fluctuation is bounded by the same full matrix
operator norm, with no dimension loss. -/
theorem full_block_normalized_trace_abs_le_euclidean_opNorm (A : FullBlockMat 2) :
    |Matrix.trace A / 4| ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := by
  have hframe (B : BlockMat 2) : frameMatrix 1 B = B := by
    cases B
    simp [frameMatrix]
  have htrace := full_response_trace_eq_four_orthonormal_loads 1 (ofFullBlockMat A)
  rw [hframe, toFullBlockMat_ofFullBlockMat] at htrace
  have hunit (i : Fin 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
      dotProduct (toFullBlockVec (orthonormalFrameLoad i ε))
        (toFullBlockVec (orthonormalFrameLoad i ε)) = 1 := by
    rw [dotProduct_toFullBlockVec]
    simpa using orthonormalFrameLoad_inner i i ε ε hε hε
  have hload (i : Fin 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
      |blockVecDot (orthonormalFrameLoad i ε)
          (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i ε))| ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := by
    have hq := full_matrix_quadratic_abs_le_euclidean_opNorm A
      (toFullBlockVec (orthonormalFrameLoad i ε))
    rw [hunit i ε hε] at hq
    have he := fullMatrixQuadratic_block (ofFullBlockMat A) (orthonormalFrameLoad i ε)
    rw [toFullBlockMat_ofFullBlockMat] at he
    rw [← he]
    simpa only [mul_one] using hq
  have hp (i : Fin 2) :
      |blockVecDot (orthonormalFrameLoad i 1)
          (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i 1))| ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := hload i 1 (Or.inl rfl)
  have hm (i : Fin 2) :
      |blockVecDot (orthonormalFrameLoad i (-1))
          (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i (-1)))| ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := hload i (-1) (Or.inr rfl)
  have hsum : |Matrix.trace A| ≤
      4 * ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := by
    rw [htrace]
    calc
      |∑ i : Fin 2,
          (blockVecDot (orthonormalFrameLoad i 1)
              (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i 1)) +
            blockVecDot (orthonormalFrameLoad i (-1))
              (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i (-1))))|
        ≤ ∑ i : Fin 2,
            |blockVecDot (orthonormalFrameLoad i 1)
                (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i 1)) +
              blockVecDot (orthonormalFrameLoad i (-1))
                (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i (-1)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2,
            (|blockVecDot (orthonormalFrameLoad i 1)
                (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i 1))| +
              |blockVecDot (orthonormalFrameLoad i (-1))
                (blockMatVecMul (ofFullBlockMat A) (orthonormalFrameLoad i (-1)))|) :=
          Finset.sum_le_sum (fun i _ => abs_add_le _ _)
      _ ≤ ∑ i : Fin 2,
            (‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ +
              ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) :=
          Finset.sum_le_sum (fun i _ => add_le_add (hp i) (hm i))
      _ = 4 * ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := by
        simp only [Fin.sum_univ_two]
        ring
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by simpa [mul_comm] using hsum)

end ASDExplicitGamma.Inverse

module

public import ASDExplicitGamma.Inverse.HybridFullTraceComparison
public import ASDExplicitGamma.Inverse.FullResponseCongruence

/-! The actual common planar map acts on both full-trace load families with
the same Euclidean operator norm. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization ASDExplicitGamma.Variational
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Moving a pair of planar maps from a loading into the four blocks is an
exact quadratic congruence identity. -/
private theorem full_block_quadratic_planar_congruence
    (A : BlockMat 2) (C D : Mat 2) (p q : Vec 2) :
    blockVecDot (matVecMul C p, matVecMul D q)
      (blockMatVecMul A (matVecMul C p, matVecMul D q)) =
    blockVecDot (p, q)
      (blockMatVecMul
        { upperLeft := C.transpose * A.upperLeft * C
          upperRight := C.transpose * A.upperRight * D
          lowerLeft := D.transpose * A.lowerLeft * C
          lowerRight := D.transpose * A.lowerRight * D } (p, q)) := by
  have hform (X Y Z : Mat 2) (x y : Vec 2) :
      vecDot (matVecMul X x) (matVecMul Y (matVecMul Z y)) =
        vecDot x (matVecMul (X.transpose * Y * Z) y) := by
    change dotProduct (X.mulVec x) (Y.mulVec (Z.mulVec y)) =
      dotProduct x ((X.transpose * Y * Z).mulVec y)
    rw [dotProduct_comm]
    rw [← Matrix.dotProduct_transpose_mulVec X x (Y.mulVec (Z.mulVec y))]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [blockVecDot, blockMatVecMul, vecDot_add_right]
  rw [hform C A.upperLeft C p p, hform C A.upperRight D p q,
    hform D A.lowerLeft C q p, hform D A.lowerRight D q q]

/-- The actual common planar map on the four full-trace loads is the block
congruence of the cell response matrix. -/
private noncomputable def fullResponsePlanarCongruence
    (A : BlockMat 2) (C D : Mat 2) : BlockMat 2 :=
  { upperLeft := C.transpose * A.upperLeft * C
    upperRight := C.transpose * A.upperRight * D
    lowerLeft := D.transpose * A.lowerLeft * C
    lowerRight := D.transpose * A.lowerRight * D }

/-- The four transformed full-trace load energies sum to the congruences of
the two diagonal response blocks. The two signs cancel both cross blocks. -/
theorem hybrid_full_trace_cell_load_sum_eq (σ : ℝ) (A : BlockMat 2)
    (C : Mat 2) (hσ : 0 < σ) :
    (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A C j) =
      σ⁻¹ * Matrix.trace (C.conjTranspose * A.upperLeft * C) +
        σ * Matrix.trace ((planarFluxMatrix C).conjTranspose * A.lowerRight *
          planarFluxMatrix C) := by
  classical
  let D := planarFluxMatrix C
  let A' := fullResponsePlanarCongruence A C D
  have hload (j : Fin 2 × Bool) :
      hybridFullTraceCellLoadEnergy σ A C j =
        hybridFullTraceLoadEnergy σ A' j := by
    dsimp [hybridFullTraceCellLoadEnergy, hybridFullTraceLoadEnergy,
      fullResponseTraceLoad, A', D]
    exact full_block_quadratic_planar_congruence A C (planarFluxMatrix C)
      ((Real.sqrt σ)⁻¹ • (orthonormalFrameLoad j.1 (if j.2 then 1 else -1)).1)
      (Real.sqrt σ • (orthonormalFrameLoad j.1 (if j.2 then 1 else -1)).2)
  calc
    _ = ∑ j : Fin 2 × Bool, hybridFullTraceLoadEnergy σ A' j := by
      exact Finset.sum_congr rfl fun j _ => hload j
    _ = Matrix.trace (toFullBlockMat (frameMatrix σ A')) :=
      (full_response_frame_trace_eq_scaled_loads σ A' hσ).symm
    _ = σ⁻¹ * Matrix.trace (C.transpose * A.upperLeft * C) +
        σ * Matrix.trace (D.transpose * A.lowerRight * D) := by
      simp [Matrix.trace, toFullBlockMat, frameMatrix, A',
        fullResponsePlanarCongruence, Fintype.sum_sum_type,
        Fin.sum_univ_two, Matrix.diag_apply] <;> ring
    _ = σ⁻¹ * Matrix.trace (C.conjTranspose * A.upperLeft * C) +
        σ * Matrix.trace (D.conjTranspose * A.lowerRight * D) := by
      rfl
    _ = _ := by rfl

/-- The full framed trace on one hybrid cell after applying the common
potential and planar solenoidal-flux maps costs at most twice the squared
gradient norm times the untransformed cell trace. -/
theorem hybrid_full_trace_cell_load_sum_le (σ : ℝ) (A : BlockMat 2)
    (C : Mat 2) (hσ : 0 < σ)
    (hUL : A.upperLeft.PosSemidef) (hLR : A.lowerRight.PosSemidef) :
    (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A C j) ≤
      (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
        Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  rw [hybrid_full_trace_cell_load_sum_eq σ A C hσ]
  exact full_response_diagonal_congruence_trace_le A C (planarFluxMatrix C)
    σ hσ hUL hLR (by rw [planar_flux_matrix_norm])

end
end ASDExplicitGamma.Inverse

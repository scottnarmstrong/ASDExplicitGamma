module

public import ASDExplicitGamma.Inverse.ClippedMatrixSource

/-! Full clipped response means at the genuine protected source cells. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise

/-- Arbitrary measurable clipping preserves the protected full-matrix 29/25 cap.
The clipping is allowed to depend on every old descendant response. -/
theorem clipped_source_mean_le (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n - 40) (hg : 0 < M.gamma) (hgmax : M.gamma ≤ gammaZero)
    (hbuf : bufferMean M n ≤ ENNReal.ofReal (8 / 25 * theta M))
    (E : Set (Cutoff.CutoffSample 2)) (hE : MeasurableSet E) (v : BlockCoord 2 → ℝ) :
    fullMatrixQuadratic v
      (∫ ω, E.indicator (clippedSourceMatrix M n Q) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (29 / 25 : ℝ) * dotProduct v v := by
  have hclip := clipped_matrix_integral_quadratic_le (Cutoff.cutoffSampleLaw M).toMeasure
    (clippedSourceMatrix M n Q) (clipped_source_integrable M n Q)
    (Filter.Eventually.of_forall (fun ω v => clipped_source_quadratic_nonneg M n Q ω v)) E hE v
  apply hclip.trans
  rw [clipped_source_integral]
  obtain ⟨alpha, beta, _, _, _, _, hcap⟩ := reset_full_matrix_mean M n hg hgmax hbuf
  have hc := (hcap (triadicCubeShift Q)).2 (ofFullBlockVec v)
  have he : translateSet (triadicCubeShift Q) (cubeSet (originCube 2 (n - 40))) = cubeSet Q := by
    rw [← hQ, ← cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [he] at hc
  have hquad := fullMatrixQuadratic_block
    (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
      (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M n) (cubeSet Q))) (ofFullBlockVec v)
  rw [toFullBlockVec_ofFullBlockVec] at hquad
  rw [hquad]
  have hid : blockVecDot (ofFullBlockVec v)
      (blockMatVecMul (Book.Ch02.blockDiag ((29 / 25 : ℝ) • (1 : Mat 2))
        ((29 / 25 : ℝ) • (1 : Mat 2))) (ofFullBlockVec v)) =
        (29 / 25 : ℝ) * dotProduct v v := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_ofFullBlockVec,
      toFullBlockVec_blockMatVecMul]
    simp only [toFullBlockMat, Book.Ch02.blockDiag, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, ofFullBlockVec, Matrix.smul_apply,
      Matrix.one_apply, Matrix.zero_apply, smul_eq_mul, toFullBlockVec]
    norm_num
    ring
  linarith only [hc, hid]

end ASDExplicitGamma.Inverse

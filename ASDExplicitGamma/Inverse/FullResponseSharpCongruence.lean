module

public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import Mathlib.Analysis.Matrix.Order

/-! Exact operator-norm payment for the active full-response trace. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization ASDExplicitGamma.Variational
open scoped MatrixOrder Matrix.Norms.Elementwise

noncomputable section

/-- A positive response block pays precisely the squared operator norm of
the common slope in its trace, with no dimension factor. -/
theorem planar_trace_congruence_sharp_le (A C : Mat 2)
    (hA : A.PosSemidef) :
    Matrix.trace (C.conjTranspose * A * C) ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 * Matrix.trace A := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hstar :
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C.conjTranspose‖ =
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖ := by
    change ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (star C)‖ = _
    rw [map_star]
    change ‖ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C)‖ = _
    exact LinearIsometryEquiv.norm_map _ _
  have hrow (i : Fin 2) :
      ∑ j : Fin 2, (B * C) i j ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 *
          ∑ j : Fin 2, B i j ^ 2 := by
    let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (B i)
    have hop := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C.conjTranspose).le_opNorm v
    rw [hstar] at hop
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hop
    have heq : (C.conjTranspose).mulVec (B i) = fun j => (B * C) i j := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        star_trivial, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Matrix.toEuclideanCLM_toLp, heq, mul_pow,
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
    simpa only [v, WithLp.ofLp_toLp] using hsq
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hrow i)
  rw [← Finset.mul_sum] at hsum
  rw [hB]
  have htrace (D : Mat 2) : Matrix.trace (D.conjTranspose * D) =
      ∑ i : Fin 2, ∑ j : Fin 2, D i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_trivial, ← sq]
    exact Finset.sum_comm
  have hprod : C.conjTranspose * (star B * B) * C =
      (B * C).conjTranspose * (B * C) := by
    simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
    noncomm_ring
  rw [hprod, htrace]
  change _ ≤ _ * Matrix.trace (B.conjTranspose * B)
  rw [htrace]
  exact hsum

/-- Separate potential and planar flux maps with the same operator bound
preserve the sharp full-trace coefficient. -/
theorem full_response_diagonal_congruence_trace_sharp_le (A : BlockMat 2)
    (C D : Mat 2) (σ : ℝ) (hσ : 0 < σ)
    (hUL : A.upperLeft.PosSemidef) (hLR : A.lowerRight.PosSemidef)
    (hD : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) D‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖) :
    σ⁻¹ * Matrix.trace (C.conjTranspose * A.upperLeft * C) +
        σ * Matrix.trace (D.conjTranspose * A.lowerRight * D) ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 *
        Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  have hULc := planar_trace_congruence_sharp_le A.upperLeft C hUL
  have hLRc := planar_trace_congruence_sharp_le A.lowerRight D hLR
  have hDsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hD
  have hLRc' := hLRc.trans (mul_le_mul_of_nonneg_right hDsq hLR.trace_nonneg)
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hULc (inv_nonneg.mpr hσ.le))
    (mul_le_mul_of_nonneg_left hLRc' hσ.le)
  have htrace : Matrix.trace (toFullBlockMat (frameMatrix σ A)) =
      σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
    simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.diag_apply]
    ring
  exact hh.trans_eq (by rw [htrace]; ring)

/-- The actual four transformed loads cost the squared slope norm times
the untransformed full trace. The final normalization by four is exact. -/
theorem hybrid_full_trace_cell_load_sum_sharp_le (σ : ℝ) (A : BlockMat 2)
    (C : Mat 2) (hσ : 0 < σ)
    (hUL : A.upperLeft.PosSemidef) (hLR : A.lowerRight.PosSemidef) :
    (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A C j) ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 *
        Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  rw [hybrid_full_trace_cell_load_sum_eq σ A C hσ]
  exact full_response_diagonal_congruence_trace_sharp_le A C (planarFluxMatrix C)
    σ hσ hUL hLR (by rw [planar_flux_matrix_norm])

end
end ASDExplicitGamma.Inverse

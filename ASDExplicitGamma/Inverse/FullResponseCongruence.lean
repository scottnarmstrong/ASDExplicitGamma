module

public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! Planar changes of potential and flux coordinates control the full trace
by the Euclidean operator norm of the common slope. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization ASDExplicitGamma.Variational
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- For a positive semidefinite planar response block, congruence by a matrix
costs at most twice the squared Euclidean operator norm in the trace. -/
theorem planar_trace_congruence_le (A C : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) :
    Matrix.trace (C.conjTranspose * A * C) ≤
      (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) * Matrix.trace A := by
  classical
  let J : Matrix (Fin 2) (Fin 2) ℝ := ASDExplicitGamma.Response.responsePlanarJ
  have hSym : A 0 1 = A 1 0 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 1) hA.1.eq
    simpa [Matrix.conjTranspose_apply] using hh.symm
  have hJ : J.conjTranspose * A * J =
      Matrix.trace A • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [J, ASDExplicitGamma.Response.responsePlanarJ, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.trace, Matrix.conjTranspose, hSym]
  let B := Matrix.trace A • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A
  have hB : B.PosSemidef := by
    change (Matrix.trace A • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A).PosSemidef
    rw [← hJ]
    exact hA.conjTranspose_mul_mul_same J
  have hquad (x : Fin 2 → ℝ) :
      dotProduct x (A.mulVec x) ≤ Matrix.trace A * dotProduct x x := by
    have hp := hB.dotProduct_mulVec_nonneg x
    have heq : dotProduct x (B.mulVec x) =
        Matrix.trace A * dotProduct x x - dotProduct x (A.mulVec x) := by
      simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] <;> ring
    have hp' : 0 ≤ dotProduct x (B.mulVec x) := by simpa using hp
    rw [heq] at hp'
    linarith
  let e (j : Fin 2) : Fin 2 → ℝ := Pi.single j 1
  have htrace : Matrix.trace (C.conjTranspose * A * C) =
      ∑ j : Fin 2, dotProduct (C.mulVec (e j)) (A.mulVec (C.mulVec (e j))) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose, Matrix.mulVec,
      dotProduct, e, Fin.sum_univ_two] <;> ring
  have hcol (j : Fin 2) :
      dotProduct (C.mulVec (e j)) (A.mulVec (C.mulVec (e j))) ≤
        Matrix.trace A * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 := by
    have hq := hquad (C.mulVec (e j))
    have hop := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C).le_opNorm
      (WithLp.toLp 2 (e j) : EuclideanSpace ℝ (Fin 2))
    have he : ‖WithLp.toLp 2 (e j)‖ = 1 := by
      fin_cases j <;> simp [EuclideanSpace.norm_eq, e, Pi.single, Fin.sum_univ_two]
    have hc : ‖WithLp.toLp 2 (C.mulVec (e j))‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖ := by
      calc
        ‖WithLp.toLp 2 (C.mulVec (e j))‖ =
            ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C)
              (WithLp.toLp 2 (e j))‖ := by rw [Matrix.toEuclideanCLM_toLp]
        _ ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖ *
            ‖WithLp.toLp 2 (e j)‖ := hop
        _ = _ := by rw [he]; ring
    have hnorm : dotProduct (C.mulVec (e j)) (C.mulVec (e j)) =
        ‖WithLp.toLp 2 (C.mulVec (e j))‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [dotProduct, Fin.sum_univ_two] <;> ring
    have htr : 0 ≤ Matrix.trace A := hA.trace_nonneg
    have hsq : ‖WithLp.toLp 2 (C.mulVec (e j))‖^2 ≤
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hc
    calc
      _ ≤ Matrix.trace A * ‖WithLp.toLp 2 (C.mulVec (e j))‖^2 := by
        rw [← hnorm]
        exact hq
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq htr
  rw [htrace, Fin.sum_univ_two]
  have h0 := hcol 0
  have h1 := hcol 1
  nlinarith [hA.trace_nonneg,
    sq_nonneg (‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖)]

/-- The framed full trace after separate potential and solenoidal-flux
coordinate changes. If the two planar maps have the same operator bound,
the trace is at most twice its square times the original framed trace. -/
theorem full_response_diagonal_congruence_trace_le (A : BlockMat 2)
    (C D : Matrix (Fin 2) (Fin 2) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hUL : A.upperLeft.PosSemidef) (hLR : A.lowerRight.PosSemidef)
    (hD : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) D‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖) :
    σ⁻¹ * Matrix.trace (C.conjTranspose * A.upperLeft * C) +
        σ * Matrix.trace (D.conjTranspose * A.lowerRight * D) ≤
      (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
        Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  have hC : 0 ≤ 2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 := by positivity
  have hσ0 : 0 ≤ σ := hσ.le
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hULc := planar_trace_congruence_le A.upperLeft C hUL
  have hLRc := planar_trace_congruence_le A.lowerRight D hLR
  have hDsq : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) D‖^2 ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hD
  have hLRtr : 0 ≤ Matrix.trace A.lowerRight := hLR.trace_nonneg
  have hLRc' : Matrix.trace (D.conjTranspose * A.lowerRight * D) ≤
      (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
        Matrix.trace A.lowerRight := by
    calc
      _ ≤ (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) D‖^2) *
          Matrix.trace A.lowerRight := hLRc
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDsq (by norm_num)) hLRtr
  have hleft := mul_le_mul_of_nonneg_left hULc hσi
  have hright := mul_le_mul_of_nonneg_left hLRc' hσ0
  have htrace : Matrix.trace (toFullBlockMat (frameMatrix σ A)) =
      σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
    simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.diag_apply] <;> ring
  calc
    _ ≤ σ⁻¹ * ((2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
          Matrix.trace A.upperLeft) +
        σ * ((2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
          Matrix.trace A.lowerRight) := add_le_add hleft hright
    _ = _ := by rw [htrace]; ring

end
end ASDExplicitGamma.Inverse

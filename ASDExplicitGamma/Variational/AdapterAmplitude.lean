module

public import ASDExplicitGamma.Variational.TraceDefect

@[expose] public section

open Homogenization

namespace ASDExplicitGamma.Variational

/-- The polarization defining the public coarse matrix is symmetric, even
before the quadratic representation is used. -/
theorem coarseBlockMatrix_symmetric {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    IsSymmetricBlockMat (coarseBlockMatrix U a) := by
  have hs (α β : BlockCoord d) : coarseBlockEntry U a α β = coarseBlockEntry U a β α := by
    unfold coarseBlockEntry
    by_cases h : α = β
    · subst β; rfl
    · rw [dite_eq_right h, dite_eq_right (Ne.symm h), add_comm (blockBasis α) (blockBasis β)]
      ring
  intro α β
  cases α <;> cases β <;>
    simpa only [blockMatEntry, coarseBlockMatrix] using hs _ _

/-- The quadratic form under amplitude congruence is the rescaled-load form. -/
theorem blockVecDot_coarseMatrixRescale_eq {d : ℕ} (A : BlockMat d)
    (P : BlockVec d) {s : ℝ} (hs : s ≠ 0) :
    blockVecDot P (blockMatVecMul (coarseMatrixRescale s A) P) =
      blockVecDot (loadRescale s P) (blockMatVecMul A (loadRescale s P)) := by
  simp only [coarseMatrixRescale, loadRescale, blockVecDot, blockMatVecMul,
    matVecMul_smul, smul_matVecMul, vecDot_add_right, vecDot_smul_left, vecDot_smul_right]
  field_simp [hs]

private theorem coarseMatrixRescale_symmetric {d : ℕ} (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) (s : ℝ) : IsSymmetricBlockMat (coarseMatrixRescale s A) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      have h := hA (Sum.inl i) (Sum.inl j)
      change A.upperLeft i j = A.upperLeft j i at h
      change s ^ 2 * A.upperLeft i j = s ^ 2 * A.upperLeft j i
      rw [h]
    | inr j => exact hA (Sum.inl i) (Sum.inr j)
  | inr i =>
    cases β with
    | inl j => exact hA (Sum.inr i) (Sum.inl j)
    | inr j =>
      have h := hA (Sum.inr i) (Sum.inr j)
      change A.lowerRight i j = A.lowerRight j i at h
      change s ^ (-2 : ℤ) * A.lowerRight i j = s ^ (-2 : ℤ) * A.lowerRight j i
      rw [h]

/-- MO-COARSE-CONGRUENCE with arbitrary positive molecular lower bound. -/
theorem coarseBlockMatrix_sq_smul_elliptic_triCube {Q : TriadicCube 2}
    {ν Λ : ℝ} {a : CoeffField 2} (hν : 0 < ν)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) {s : ℝ} (hs : 0 < s) :
    coarseBlockMatrix (cubeSet Q) (s ^ 2 • a) =
      coarseMatrixRescale s (coarseBlockMatrix (cubeSet Q) a) := by
  apply Eq.symm
  apply eq_coarseBlockMatrix_of_isCoarseBlockMatrix
  refine ⟨coarseMatrixRescale_symmetric _ (coarseBlockMatrix_symmetric _ _) s, ?_⟩
  intro P
  rw [Mu_sq_smul_eq hEll (measurableSet_cubeSet Q) hs,
    mu_eq_half_coarseBlockMatrix_elliptic_triCube hν hEll,
    blockVecDot_coarseMatrixRescale_eq _ _ hs.ne']

/-- Exact positive-amplitude coarse congruence, with D_c's square-root factors. -/
theorem coarseBlockMatrix_smul_elliptic_triCube {Q : TriadicCube 2}
    {ν Λ c : ℝ} {a : CoeffField 2} (hν : 0 < ν)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (hc : 0 < c) :
    coarseBlockMatrix (cubeSet Q) (c • a) =
      coarseMatrixRescale (Real.sqrt c) (coarseBlockMatrix (cubeSet Q) a) := by
  have h := coarseBlockMatrix_sq_smul_elliptic_triCube hν hEll (Real.sqrt_pos.mpr hc)
  simpa only [Real.sq_sqrt hc.le] using h

end ASDExplicitGamma.Variational

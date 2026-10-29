module

public import ASDExplicitGamma.Main.AffineMatrixMoments

/-! Trace identities for the actual stationary partial-insertion response means. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open Homogenization.Book.Ch04

noncomputable section

/-- The actual partial-insertion mean response blocks are scalar, and their
matrix traces are twice the corresponding scalar means. -/
theorem mainInsertionCoefficientLaw_expectedBlockTrace_scalars
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ k d : ℝ,
      (∀ i j : Fin 2,
        ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft i j ∂
          mainInsertionCoefficientLaw M m t = if i = j then k else 0) ∧
      (∀ i j : Fin 2,
        ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight i j ∂
          mainInsertionCoefficientLaw M m t = if i = j then d else 0) ∧
      (∫ a, Matrix.trace
        (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft ∂
          mainInsertionCoefficientLaw M m t = 2 * k) ∧
      (∫ a, Matrix.trace
        (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight ∂
          mainInsertionCoefficientLaw M m t = 2 * d) := by
  obtain ⟨k, d, hUL, hLR⟩ :=
    mainInsertionCoefficientLaw_expectedDiagonalBlocks_areScalar M m n t ht
  let P := mainInsertionCoefficientLaw M m t
  let Q := originCube 2 n
  let ul0 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 0 0
  let ul1 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 1 1
  let lr0 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0
  let lr1 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 1 1
  have hIntUL0 : Integrable ul0 P := by
    have h := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q
      (Sum.inl 0) (Sum.inl 0)
    simpa [ul0, P, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
      using h
  have hIntUL1 : Integrable ul1 P := by
    have h := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q
      (Sum.inl 1) (Sum.inl 1)
    simpa [ul1, P, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
      using h
  have hIntLR0 : Integrable lr0 P := by
    have h := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q
      (Sum.inr 0) (Sum.inr 0)
    simpa [lr0, P, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
      using h
  have hIntLR1 : Integrable lr1 P := by
    have h := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q
      (Sum.inr 1) (Sum.inr 1)
    simpa [lr1, P, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
      using h
  have hUL0 : ∫ a, ul0 a ∂P = k := by
    simpa [ul0, P, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
      hUL (0 : Fin 2) 0
  have hUL1 : ∫ a, ul1 a ∂P = k := by
    simpa [ul1, P, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
      hUL (1 : Fin 2) 1
  have hLR0 : ∫ a, lr0 a ∂P = d := by
    simpa [lr0, P, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
      hLR (0 : Fin 2) 0
  have hLR1 : ∫ a, lr1 a ∂P = d := by
    simpa [lr1, P, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
      hLR (1 : Fin 2) 1
  refine ⟨k, d, hUL, hLR, ?_, ?_⟩
  · calc
      ∫ a, Matrix.trace
          (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft ∂P =
          ∫ a, ul0 a + ul1 a ∂P := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun a => by
              simp [ul0, ul1, Matrix.trace, Fin.sum_univ_two]
      _ = (∫ a, ul0 a ∂P) + ∫ a, ul1 a ∂P := integral_add hIntUL0 hIntUL1
      _ = 2 * k := by rw [hUL0, hUL1]; ring
  · calc
      ∫ a, Matrix.trace
          (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight ∂P =
          ∫ a, lr0 a + lr1 a ∂P := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun a => by
              simp [lr0, lr1, Matrix.trace, Fin.sum_univ_two]
      _ = (∫ a, lr0 a ∂P) + ∫ a, lr1 a ∂P := integral_add hIntLR0 hIntLR1
      _ = 2 * d := by rw [hLR0, hLR1]; ring

end

end ASDExplicitGamma.Main

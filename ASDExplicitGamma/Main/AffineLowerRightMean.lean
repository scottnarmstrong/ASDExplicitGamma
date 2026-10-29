module

public import ASDExplicitGamma.Main.AffineActualTrace
public import ASDExplicitGamma.Native.OldSignedAffineInverseBlock
public import ASDExplicitGamma.Native.ParentBoundaryBandBlockLaw

/-! The actual OLD-frame inverse block trace is twice its scalar block mean. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Inverse
open Algsuperdiff.Section3

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- The expected OLD-frame lower-right trace on the actual depth-five source
cell is twice the literal normalized lower-right block mean. -/
theorem main_affine_lower_right_trace_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (t : ℝ) :
    (∫ ω, Matrix.trace (coarseBlockMatrix
      (cubeSet (originCube 2 (m - 5)))
      (oldSignedPartialFrameField M m 1 t ω)).lowerRight
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      2 * parentBoundaryBandBlockMean M m 1 t
        (originCube 2 (m - 5)) false := by
  let U : TriadicCube 2 := originCube 2 (m - 5)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hU : U ∈ descendantsAtDepth (originCube 2 m) 5 := by
    simpa only [U, Nat.cast_ofNat] using originCube_mem_descendantsAtDepth' 2 m 5
  have hscalar := parent_boundary_band_block_scalar_law
    M h hM m 1 (by norm_num) 5 U hU t false
  have hblock (ω : Cutoff.CutoffSample 2) :
      parentBoundaryBandNormalizedBlock M m 1 t U false ω =
        (coarseBlockMatrix (openCubeSet U)
          (oldSignedPartialFrameField M m 1 t ω)).lowerRight := by
    have h := old_signed_actual_normalized_block M m 5 U hU t ω false
    simpa only [Bool.false_eq_true, ite_false] using h
  have hpoint (ω : Cutoff.CutoffSample 2) :
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameField M m 1 t ω)).lowerRight =
        parentBoundaryBandNormalizedBlock M m 1 t U false ω (0 : Fin 2) (0 : Fin 2) +
        parentBoundaryBandNormalizedBlock M m 1 t U false ω (1 : Fin 2) (1 : Fin 2) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U]
    rw [← hblock ω]
    simp [Matrix.trace, Fin.sum_univ_two]
  have hInt (i j : Fin 2) :
      Integrable (fun ω => parentBoundaryBandNormalizedBlock
        M m 1 t U false ω i j) μ := by
    simpa [μ] using hscalar.1 i j
  have hmean (i j : Fin 2) :
      (∫ ω, parentBoundaryBandNormalizedBlock
        M m 1 t U false ω i j ∂μ) =
        if i = j then parentBoundaryBandBlockMean M m 1 t U false else 0 := by
    simpa [μ] using
      (parent_boundary_band_block_mean M h hM m 1 (by norm_num) 5 U hU t false).2 i j
  calc
    _ = ∫ ω, parentBoundaryBandNormalizedBlock
          M m 1 t U false ω (0 : Fin 2) (0 : Fin 2) +
        parentBoundaryBandNormalizedBlock M m 1 t U false ω (1 : Fin 2) (1 : Fin 2) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = (∫ ω, parentBoundaryBandNormalizedBlock
          M m 1 t U false ω (0 : Fin 2) (0 : Fin 2) ∂μ) +
        ∫ ω, parentBoundaryBandNormalizedBlock M m 1 t U false ω (1 : Fin 2) (1 : Fin 2) ∂μ :=
          integral_add (hInt 0 0) (hInt 1 1)
    _ = 2 * parentBoundaryBandBlockMean M m 1 t U false := by
          rw [hmean 0 0, hmean 1 1]
          simp
          ring

end
end ASDExplicitGamma.Main

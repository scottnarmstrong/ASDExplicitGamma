module

public import ASDExplicitGamma.Main.AffineInverseTrace
public import ASDExplicitGamma.Native.OldSignedCoarseDirectionalCells
public import ASDExplicitGamma.Scalar.CellTranslation

import Mathlib.Tactic

/-! Translation transfers the OLD-frame inverse-trace cap from the origin
source square to each source cell inside an observation square. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Inverse ASDExplicitGamma.Model ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-- Every source cell at depth `hobs + 5` in the observation square has the
same expected OLD-frame inverse-trace cap as the origin source square. -/
theorem main_affine_inverse_trace_frame_cells
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth
      (originCube 2 (m + (hobs : ℤ))) (hobs + 5)) :
    (∫ ω, (Annealed.sigmaBar M m : ℝ) *
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 2 * mainBeta := by
  have hscale : U.scale = m - 5 := by
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale = (m + (hobs : ℤ)) - ((hobs + 5 : ℕ) : ℤ) at hh
    push_cast at hh
    omega
  have hpoint (ω : Cutoff.CutoffSample 2) :
      (Annealed.sigmaBar M m : ℝ) *
          Matrix.trace (coarseBlockMatrix (cubeSet U)
            (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight =
        (Annealed.sigmaBar M m : ℝ) *
          Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
            (Model.partialInsertedCoefficient M m t
              (triadicCubeShift U +ᵥ ω)).toFun).lowerRight := by
    rw [old_signed_partial_coarse_cell_translate, hscale]
  have hfun :
      (fun ω => (Annealed.sigmaBar M m : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet U)
          (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight) =
      (fun ω => (Annealed.sigmaBar M m : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
          (Model.partialInsertedCoefficient M m t
            (triadicCubeShift U +ᵥ ω)).toFun).lowerRight) := by
    funext ω
    exact hpoint ω
  calc
    (∫ ω, (Annealed.sigmaBar M m : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet U)
          (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, (Annealed.sigmaBar M m : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
          (Model.partialInsertedCoefficient M m t
            (triadicCubeShift U +ᵥ ω)).toFun).lowerRight
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
          rw [hfun]
    _ = ∫ ω, (Annealed.sigmaBar M m : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
          (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
          simpa only using integral_cutoffSample_vadd M (triadicCubeShift U)
            (fun ω => (Annealed.sigmaBar M m : ℝ) *
              Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
                (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight)
    _ ≤ 2 * mainBeta :=
      main_affine_inverse_trace_frame_integral M h hM hgamma N hpast m hm t ht

end
end ASDExplicitGamma.Main

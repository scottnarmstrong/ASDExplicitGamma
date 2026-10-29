module

public import ASDExplicitGamma.Main.HotTrialExpectationsSplit
public import ASDExplicitGamma.Main.HotEOscillationDepthFiveProfile
public import ASDExplicitGamma.Main.HotPatchGap

/-! Package D at the observer root `Q' = originCube 2 (m + hobs)` tiled to depth
`hobs + 5` (cells at scale `m - 5`): the actual-law energy drop. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- Observer-root energy drop: depth-`hobs+5` average of the actual four-load traces
minus the actual observer-root trace. -/
def mainHotDropObs (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
      (fun U => rawCubeFourLoadTrace M m U t ω) -
    rawCubeFourLoadTrace M m (originCube 2 (m + hobs)) t ω

/-- On every descendant cell of any root, the raw four-load trace is the framed trace of
the actual response coefficient. -/
theorem main_hot_trace_eq_frame_trace_obs
    (M : ABKModel 2) (m : ℤ) (Qroot : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Qroot j) :
    rawCubeFourLoadTrace M m U t ω =
      traceDefect (openCubeSet U)
        (oldSignedPartialFrameFieldAt M Qroot m t ω) 1 := by
  unfold rawCubeFourLoadTrace traceDefect
  rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
    old_signed_partial_cell_frame_at M Qroot m t ω U j hU]
  simp only [Variational.frameMatrix, inv_one, one_mul, Matrix.trace_smul,
    smul_eq_mul]

/-- Pathwise, the observer drop is the trace subadditivity defect of the actual
partial frame, hence the four-load energy of the patch drop, hence nonnegative. -/
theorem main_hot_drop_obs_pathwise
    (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    mainHotDropObs M m hobs t ω =
      ∑ c : BlockCoord 2, oldSignedEnergyPairing (originCube 2 (m + hobs))
        M.nu (Annealed.sigmaBar M m : ℝ) (mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
          (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs))))
            m t ω))
        (hotPatchDrop (originCube 2 (m + hobs)) (hobs + 5) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
            (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs))))
              m t ω)) (blockBasis c))
        (hotPatchDrop (originCube 2 (m + hobs)) (hobs + 5) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
            (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs))))
              m t ω)) (blockBasis c)) ∧
    0 ≤ mainHotDropObs M m hobs t ω := by
  classical
  let Q := originCube 2 (m + hobs)
  let k := mainAffineOpenResponseRestriction Q
    (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)
  have hsum := hot_patch_drop_energy_sum Q (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have hroot : Q ∈ descendantsAtDepth Q 0 := by
    simp only [descendantsAtDepth_zero, Finset.mem_singleton]
  have hcells : descendantsAverage Q (hobs + 5) (fun U => rawCubeFourLoadTrace M m U t ω) =
      descendantsAverage Q (hobs + 5) (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) 1) := by
    refine main_hot_descendants_average_congr _ _ _ _ ?_
    intro U hU
    exact main_hot_trace_eq_frame_trace_obs M m Q t ω (hobs + 5) U hU
  have hr : rawCubeFourLoadTrace M m Q t ω = traceDefect (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) 1 :=
    main_hot_trace_eq_frame_trace_obs M m Q t ω 0 Q hroot
  have heq : mainHotDropObs M m hobs t ω =
      descendantsAverage Q (hobs + 5) (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) 1) -
        traceDefect (openCubeSet Q)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) 1 := by
    unfold mainHotDropObs
    rw [hcells, hr]
  refine ⟨?_, ?_⟩
  · rw [heq, ← hsum]
  · rw [heq, ← hsum]
    exact Finset.sum_nonneg fun c _ =>
      old_signed_energy_pairing_nonneg Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k _

end

end ASDExplicitGamma.Main

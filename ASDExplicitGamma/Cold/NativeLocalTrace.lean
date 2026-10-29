module

public import ASDExplicitGamma.Cold.NativeSharpLocalIndependence
public import ASDExplicitGamma.Cold.NativeCellTrace

/-! # Genuine integral-local measurability of the fixed-frame trace -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
namespace ASDExplicitGamma.Cold

/-- The actual trace variable reads only its cell's completed integral-local information. -/
theorem coldNativeCellTrace_local (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    @Measurable (CutoffSample 2) ℝ (cutoffSampleLocalSigma M m (cubeSet Q)) (borel ℝ)
      (coldNativeCellTrace M m Q) := by
  have hUL : @Measurable (CutoffSample 2) ℝ (cutoffSampleLocalSigma M m (cubeSet Q)) (borel ℝ)
      (fun ω => Matrix.trace (coarseBlockMatrix (cubeSet Q) (coefficientCutoff M.nu m ω).toFun).upperLeft) := by
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro i _
    exact measurable_coarseB_apply_cutoffSampleLocal M m Q Set.Subset.rfl i i
  have hLR : @Measurable (CutoffSample 2) ℝ (cutoffSampleLocalSigma M m (cubeSet Q)) (borel ℝ)
      (fun ω => Matrix.trace (coarseBlockMatrix (cubeSet Q) (coefficientCutoff M.nu m ω).toFun).lowerRight) := by
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro i _
    exact measurable_coarseSigmaStarInv_apply_cutoffSampleLocal M m Q Set.Subset.rfl i i
  exact ((hUL.const_mul (Annealed.sigmaBar M m:ℝ)⁻¹).add
    (hLR.const_mul (Annealed.sigmaBar M m:ℝ))).sub_const 4

end ASDExplicitGamma.Cold

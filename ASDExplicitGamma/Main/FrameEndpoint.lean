module

public import ASDExplicitGamma.Main.FrameAlgebra
public import ASDExplicitGamma.Main.HeatIdentity

/-! The completed endpoint, with scalar structural continuity kept explicit. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization Algsuperdiff.Section3 MeasureTheory ASDExplicitGamma.Gaussian

/-- Transport of a completed coefficient-law integral to the actual cutoff
sample law, including measurability of the coarse trace. -/
theorem main_completed_trace_integral_eq (M : ABKModel 2) (k n : ℤ) (sigma : ℝ) :
    (∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 n)) a.toFun sigma
      ∂(Cutoff.coefficientCutoffLaw M k)) =
    ∫ omega, traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu k omega).toFun sigma ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := Variational.integrable_traceDefect_cutoffLaw M k (originCube 2 n) sigma
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  exact integral_map (Cutoff.measurable_coefficientCutoff M.nu k).aemeasurable hi.aestronglyMeasurable

/-- The actual time-one insertion is exactly the completed next law in the
OLD frame; structural restoration is deliberately a subsequent step. -/
theorem mainInsertionTrace_one_integral (M : ABKModel 2) (m n : ℤ) :
    modelTraceHeatAverage n M m 1 =
      ∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 n)) a.toFun
        (Annealed.sigmaBar M m : ℝ) ∂(Cutoff.coefficientCutoffLaw M (m + 1)) := by
  rw [main_completed_trace_integral_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega => by
    simp only [mainInsertion_coefficient_one]

/-- The full completed-endpoint frame adapter. The source scalar-continuity
ratio is the only undischarged input; no ratio is assigned to a partial law. -/
theorem main_completed_endpoint_return_of_ratio (M : ABKModel 2) (m n : ℤ) (R : ℝ)
    (hr : 1 ≤ (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ))
    (hR : (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) ≤ R) :
    (∫ omega, cutoffTraceDefect M (m + 1) n omega ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      R * modelTraceHeatAverage n M m 1 := by
  rw [mainInsertionTrace_one_integral]
  change (∫ omega, traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu (m + 1) omega).toFun (Annealed.sigmaBar M (m + 1) : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ _
  rw [← main_completed_trace_integral_eq]
  exact main_completed_frame_return_of_ratio M (m + 1) n (Annealed.sigmaBar M m : ℝ) R
    (Annealed.sigmaBar M m).2 hr hR

end ASDExplicitGamma.Main

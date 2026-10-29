module

public import ASDExplicitGamma.Native.OldSignedCoarseDirectionalCells

/-! Actual expected directional half-trace on the common descendant tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Algsuperdiff.Section3
noncomputable section

/-- Integration commutes with the genuine finite descendant average. -/
theorem old_signed_integral_descendants_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : TriadicCube 2) (depth : ℕ) (F : TriadicCube 2 → Ω → ℝ)
    (hF : ∀ U ∈ descendantsAtDepth Q depth,Integrable (F U) μ) :
    (∫ ω,descendantsAverage Q depth (fun U => F U ω) ∂μ)=
      descendantsAverage Q depth (fun U => ∫ ω,F U ω ∂μ) := by
  unfold descendantsAverage
  dsimp only
  rw [integral_const_mul,integral_finsetSum _ hF]

/-- Actual sample integrability of the coarse directional quadratic on an
arbitrary cell, obtained from the proved coefficient-law integrability. -/
theorem old_signed_directional_sample_integrable (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (sigma : ℝ) (e : Vec 2) :
    Integrable (fun ω => vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := old_signed_coarse_directional_integrable M m t ht Q sigma e
  exact (integrable_map_measure hi.aestronglyMeasurable
    (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable).mp hi

/-- Actual sample integrability of the fixed-frame cell trace. -/
theorem old_signed_trace_sample_integrable (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (sigma : ℝ) :
    Integrable (fun ω => traceDefect (cubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := old_signed_coarse_trace_integrable M m t ht Q sigma
  exact (integrable_map_measure hi.aestronglyMeasurable
    (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable).mp hi

/-- Each depth's unweighted directional majorant has exactly the expected
half trace on the actual common tiling. No descendant independence is needed. -/
theorem old_signed_descendant_directional_mean (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (depth : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (sigma : ℝ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (descendantsAverageMat Q depth (fun U =>
      oldSignedCoarseDirectionalMatrix U (Model.partialInsertedCoefficient M m t ω).toFun sigma)) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
    (1/2 : ℝ)*(∫ ω,descendantsAverage Q depth (fun U => traceDefect (cubeSet U)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  simp_rw [vecDot_matVecMul_descendantsAverageMat]
  rw [old_signed_integral_descendants_average _ Q depth _
    (fun U _ => old_signed_directional_sample_integrable M m t ht U sigma e)]
  simp_rw [old_signed_coarse_directional_cell_mean M m _ t ht sigma e]
  rw [old_signed_integral_descendants_average _ Q depth _
    (fun U _ => old_signed_trace_sample_integrable M m t ht U sigma)]
  unfold descendantsAverage
  dsimp only
  rw [← Finset.sum_mul,← Finset.mul_sum]
  ring

end
end ASDExplicitGamma.Native

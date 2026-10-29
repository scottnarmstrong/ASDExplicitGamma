module

public import ASDExplicitGamma.Native.OldSignedCoarseDirectionalIntegrability

/-! The expected directional half-trace identity on the actual cutoff
sample carrier, rather than only on the coefficient pushforward law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Algsuperdiff.Section3
noncomputable section

/-- Pull the proved half-trace identity back to the actual inserted medium. -/
theorem old_signed_coarse_directional_sample_mean (M : ABKModel 2) (m n : ℤ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (sigma : ℝ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix (originCube 2 n)
      (Model.partialInsertedCoefficient M m t ω).toFun sigma) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
    (1/2 : ℝ)*(∫ ω,traceDefect (cubeSet (originCube 2 n))
      (Model.partialInsertedCoefficient M m t ω).toFun sigma
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  have hf := (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
  have hq := integral_map hf
    (old_signed_coarse_directional_integrable M m t ht (originCube 2 n) sigma e).aestronglyMeasurable
  have hT := integral_map hf
    (old_signed_coarse_trace_integrable M m t ht (originCube 2 n) sigma).aestronglyMeasurable
  change (∫ a,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix (originCube 2 n) a.toFun sigma) e)
    ∂mainInsertionCoefficientLaw M m t)=_ at hq
  change (∫ a,traceDefect (cubeSet (originCube 2 n)) a.toFun sigma
    ∂mainInsertionCoefficientLaw M m t)=_ at hT
  rw [←hq,old_signed_coarse_directional_mean M m n t ht sigma e,hT]

end
end ASDExplicitGamma.Native

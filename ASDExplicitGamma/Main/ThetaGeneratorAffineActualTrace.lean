module

public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeASlope
public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope
public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth

/-! The affine estimate uses the actual depth-five trace mean in the OLD
true frame. This file records its source-cell identification for MA-AFFINE. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Inverse

noncomputable section

/-- The raw source trace on the actual depth-five cell has the source's
actual-law OLD-frame mean. -/
theorem main_affine_actual_trace_mean_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    (∫ ω, traceDefect (cubeSet (originCube 2 (m - 5)))
      (Model.partialInsertedCoefficient M m t ω).toFun
      (Annealed.sigmaBar M m : ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      mainMeanActual_Th M m t := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  have hQ : originCube 2 (m - 5) ∈ descendantsAtDepth (originCube 2 m) 5 :=
    originCube_mem_descendantsAtDepth' 2 m 5
  have hscale : Q.scale = m - 5 := by
    simpa only [Q, originCube] using scale_eq_sub_of_mem_descendantsAtDepth hQ
  have hraw :
      (∫ ω, rawWeakTraceSequence M m Q t ω 0
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) = inSourceMeanActual M m 5 t := by
    simpa only [Nat.add_zero] using
      old_signed_q1_source_mean_eq M m Q hscale t ht 0
  have hpoint (ω : Cutoff.CutoffSample 2) :
      traceDefect (cubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun
          (Annealed.sigmaBar M m : ℝ) = rawWeakTraceSequence M m Q t ω 0 := by
    have hdepth := old_signed_source_trace_depth M m 5 Q hQ t ω 0
    have hzero : descendantsAverage Q 0 (fun V =>
        traceDefect (openCubeSet V) (oldSignedPartialFrameField M m 1 t ω) 1) =
        traceDefect (openCubeSet Q) (oldSignedPartialFrameField M m 1 t ω) 1 := by
      simp [descendantsAverage]
    rw [← hdepth, hzero]
    unfold traceDefect
    rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
      old_signed_partial_cell_frame M m 1 t ω Q 5 hQ]
    simp only [Variational.frameMatrix, Nat.cast_one, add_sub_cancel_right,
      inv_one, one_mul, Matrix.trace_smul, smul_eq_mul]
  calc
    _ = ∫ ω, rawWeakTraceSequence M m Q t ω 0
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
    _ = inSourceMeanActual M m 5 t := hraw
    _ = mainMeanActual_Th M m t := rfl

end

end Main


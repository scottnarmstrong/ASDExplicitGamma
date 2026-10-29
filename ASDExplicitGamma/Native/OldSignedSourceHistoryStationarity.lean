module

public import ASDExplicitGamma.Native.OldSignedSourceHistoryBudget

/-! Stationarity identifies the expectation budget on every actual source cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual fixed-frame raw trace has the origin-scale expectation. -/
theorem old_signed_raw_cube_trace_mean_eq_origin (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (t : ℝ) :
    (∫ ω,rawCubeFourLoadTrace M n Q t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ ω,rawDepthFourLoadTrace M n Q.scale t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [raw_cube_four_load_trace_eq_translated_origin_helper M n Q t]
  exact integral_cutoffSample_vadd M (triadicCubeShift Q)
    (rawDepthFourLoadTrace M n Q.scale t)

/-- The finite descendant trace average has the same first moment as its
origin descendant-scale trace; no independence is used. -/
theorem old_signed_source_trace_mean_eq_depth (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ht : 0≤t ∧ t≤1) (j : ℕ) :
    (∫ ω,rawWeakTraceSequence M n Q t ω j ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ ω,rawDepthFourLoadTrace M n (Q.scale-(j:ℤ)) t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [old_signed_raw_trace_average]
  rw [old_signed_integral_descendants_average _ Q j _
    (fun U _ => old_signed_trace_sample_integrable M n t ht U (Annealed.sigmaBar M n))]
  let c := ∫ ω,rawDepthFourLoadTrace M n (Q.scale-(j:ℤ)) t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have he : descendantsAverage Q j (fun U => ∫ ω,traceDefect (cubeSet U)
      (Model.partialInsertedCoefficient M n t ω).toFun (Annealed.sigmaBar M n)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=descendantsAverage Q j (fun _ => c) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    change (∫ ω,rawCubeFourLoadTrace M n U t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=c
    rw [old_signed_raw_cube_trace_mean_eq_origin,scale_eq_sub_of_mem_descendantsAtDepth hU]
  rw [he,descendantsAverage_const]

/-- Equal-scale source cells have identical deterministic history budgets,
including the same correlated rare reserve at every depth. -/
theorem old_signed_source_history_budget_eq_scale (M : ABKModel 2) (n : ℤ)
    (U V : TriadicCube 2) (hscale : U.scale=V.scale)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (j : ℕ) :
    oldSignedSourceHistoryBudget M n U t j=oldSignedSourceHistoryBudget M n V t j := by
  unfold oldSignedSourceHistoryBudget
  rw [old_signed_source_trace_mean_eq_depth M n U t ht j,
    old_signed_source_trace_mean_eq_depth M n V t ht j,hscale]

end
end ASDExplicitGamma.Native

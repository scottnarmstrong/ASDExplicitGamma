module

public import ASDExplicitGamma.Scalar.LowerInput
public import ASDExplicitGamma.Native.SourceChainRows
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion

/-! SC-LOWER-INPUT-BRIDGE: the corrected OLD source rows and the mixed
bridge at t=0, under the standing outer-target chronology. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native Inverse Main
noncomputable section

/-- The lower trial's OLD inputs: corrected q1, exact theta-scaled mean rows,
the sharp weak row, endpoint corollaries, and integrable mixed moments.
Every source/bank estimate is supplied internally from completed states. -/
theorem scalar_lower_input_bridge
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N, nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    nativeCompletedSourceMean M m 1 ≤ ENNReal.ofReal (theta M*(nativeBoundaryQ1Sharp:ℝ)) ∧
    nativeCompletedSourceMean M m 1 ≤ ENNReal.ofReal q1SourceTargetCap ∧
    nativeCompletedSourceMean M m 4 ≤
      ENNReal.ofReal (theta M*((nativeSourceExactMeanCaps.getD 4 0:ℚ):ℝ)) ∧
    nativeCompletedSourceMean M m 5 ≤
      ENNReal.ofReal (theta M*((nativeSourceExactMeanCaps.getD 5 0:ℚ):ℝ)) ∧
    nativeCompletedSourceWeak M m 5 ≤ ENNReal.ofReal (mixedXiPreCap M) ∧
    LowerSourceEndpointConclusion M m ∧
    (∀ k : Fin 4,
      Integrable (fun ω => mixedGlobalHistoryMax M m 0 ω^k.val*
        mixedOldTheta M m (originCube 2 m) 0 ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, mixedGlobalHistoryMax M m 0 ω^k.val*
        mixedOldTheta M m (originCube 2 m) 0 ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainBeta^k.val*(mixedXiPreCap M+(1/10^12:ℝ)*theta M)) := by
  have hSmall := native_source_smaller_gamma M h hM hg N hpast m hm
  have hRows := native_source_rows_of_smaller_gamma M m hSmall
  have hq1 := native_completed_q1_bound M h hM hg m (fun k hk => hpast k (hk.trans hm))
  refine ⟨hq1,lower_q1_endpoint_of_boundary_charge M m hg hq1,
    hRows.mean_exact ⟨4,by omega⟩,hRows.mean_exact ⟨5,by omega⟩,
    mixed_xi_pre_cap_of_smaller_gamma M m hSmall,
    lower_source_endpoint_conclusion M m hg hSmall,?_⟩
  have hMixed := mixed_bridge_root_package M h hM hg N hpast m hm 0
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
  intro k
  refine ⟨(mixed_root_old_theta_row M h hM hg N hpast m hm 0 (by norm_num) k).1,?_⟩
  simpa only [mixedXi,zero_mul,add_zero] using hMixed.1 k

end
end ASDExplicitGamma.Scalar

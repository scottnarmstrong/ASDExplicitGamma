module

public import ASDExplicitGamma.Native.SourceChainEndpoint

/-! The long-block source cap interface at an earlier completed endpoint.
It requires states through that endpoint, supplied by the outer target. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- SC-UPPER-SOURCE-CAPS: actual completed source rows and the depth-fourteen
safe mean, the complete random history in L12, and the distinct full64
response/history constants. All producer and current-endpoint state inputs
are discharged from the standing outer-target assumptions. -/
theorem scalar_upper_source_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N) :
    (∀ r : Fin 6, nativeCompletedSourceMean M n r.val ≤
      ENNReal.ofReal (sourceMeanEndpointCaps r)) ∧
    (∀ r : Fin 6, nativeCompletedSourceWeak M n r.val ≤
      ENNReal.ofReal (weakSourceEndpointCaps r)) ∧
    nativeCompletedSourceMean M n 14 ≤ ENNReal.ofReal safeDepth14EndpointCap ∧
    eLpNorm (lagTraceHistory M n 14) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (61/10 : ℝ) ∧
    invFull64Bt < (1009309/500000 : ℚ) ∧
    invFull64KD < 16684 ∧ invFull64K0 < 5899542 ∧
    invS0 < (1130469/1000000 : ℚ) ∧ invS1 < (838143/200000 : ℚ) := by
  have hsource := native_source_smaller_gamma M h hM hg N hpast n hn
  have hcaps := scalar_upper_source_caps_of_smaller_gamma M h n hg hsource
    (fun k hk => hpast k (hk.trans_lt hn))
  have hfull := scalar_upper_full64_endpoint_caps
  exact ⟨hcaps.1, hcaps.2.1, hcaps.2.2.1, hcaps.2.2.2,
    hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩

end
end ASDExplicitGamma.Scalar

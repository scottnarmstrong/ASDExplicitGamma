module

public import ASDExplicitGamma.Native.OldSignedFull64SlopeSum
public import ASDExplicitGamma.Native.OldSignedMaxHistoryMoment

/-! Transport of the actual OLD max history with the complete full64 slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Set Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Actual trace transport at each depth, using the smaller full64 bank in
the generator and the existing physical heat-integral identity. -/
theorem old_signed_full64_depth_trace_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (j : ℕ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    lpNorm (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) t) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) 0) 20 (Cutoff.cutoffSampleLaw M).toMeasure+
        t*oldSignedP20Full64Control M h n j := by
  let Q := originCube 2 (n-((5+j:ℕ):ℤ))
  let U := fun _ : ℝ => oldSignedP20Full64Control M h n j
  have hU0 : ∀ s ∈ Icc (0:ℝ) 1,0≤U s := fun _ _ => old_signed_full64_control_nonneg M h n j
  have hUInt : IntegrableOn U (Icc (0:ℝ) 1) := integrableOn_const (by rw [Real.volume_Icc]; norm_num)
  have hT0 := Main.main_rawDepthFourLoadTrace_memLp_twenty_zero_of_strong20 M n _
    (hpast n le_rfl).2.1 j
  have hTt := Main.main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame M h hM hg n hpast j t ht
  have hgen := old_signed_full64_depth_generator M h hM hg n hpast j
  have hh := Main.main_rawCube_lpNorm_twenty_bound_of_generator Q M h hM n U hU0 hUInt t ht.1 ht.2
    hgen hT0 hTt _ le_rfl
  rw [Main.main_rawCubeFourLoadTrace_lpNorm_eq_origin M n Q t 20 hTt] at hh
  simpa only [Q,originCube,U,intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hh

end
end ASDExplicitGamma.Native

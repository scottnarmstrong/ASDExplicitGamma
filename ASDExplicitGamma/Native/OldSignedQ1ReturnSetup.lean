module

public import ASDExplicitGamma.Native.OldSignedQ1SetupReadable
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps
public import ASDExplicitGamma.Native.GenericSourceBandEndpoint

/-! Exact flat boundary and completed frame coefficients of the q1 return. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Scalar Response Variational Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The frozen flat payment is twice the full one-shell variance. -/
theorem old_signed_q1_setup_b0 :
    nativeSetupQ1001B0R=2*nativeSetupQ1001FieldsR.getD 0 0 := by
  unfold nativeSetupQ1001B0R
  rw [show 348=334+14 by norm_num,old_signed_q1_setup_prefix_value]
  simp only [oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ,
    oldSignedQ1SetupNode065,oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,
    oldSignedQ1SetupNode000,old_signed_q1_setup_base_variance]
  ring

/-- The exact frame uses the exponential endpoint, without a rational enlargement. -/
theorem old_signed_q1_setup_frame :
    nativeSetupQ1001FrameR=(3:ℝ)^(2*gammaZero) := by
  unfold nativeSetupQ1001FrameR
  rw [show 392=334+58 by norm_num,old_signed_q1_setup_prefix_value]
  simp only [oldSignedQ1SetupStack080,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ,
    oldSignedQ1SetupNode021,oldSignedQ1SetupNode020,oldSignedQ1SetupNode019,
    nativeSetupInputReal,Rat.cast_div,Rat.cast_ofNat]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num only [gammaZero]

/-- The physical flat boundary cost fits the exact frozen q1 allocation. -/
theorem old_signed_q1_flat_boundary_payment
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    oldSignedFlatBoundaryEnergy (originCube 2 n) b L ≤ theta M*nativeSetupQ1001B0R := by
  intro b L
  apply (old_signed_flat_boundary_energy_bounds _ b L).2.trans
  have hh := mul_le_mul_of_nonneg_left (old_signed_q1_model_variance M h hg n hstate)
    (by norm_num : (0:ℝ) ≤ 2)
  rw [old_signed_q1_setup_b0]
  convert hh using 1
  ring

/-- The completed source returns to its true frame with the exact q1 frame factor. -/
theorem old_signed_q1_completed_frame (M : ABKModel 2) (n : ℤ) (hg : M.gamma ≤ gammaZero) :
    (∫ ω,cutoffTraceDefect M (n+1) n ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      nativeSetupQ1001FrameR*nativeSourceBandMean M n 1 1 := by
  have hratio := sigmaBar_structural_continuity_nat M n 1
  simp only [Nat.cast_one,mul_one] at hratio
  have hE : (3:ℝ)^(2*M.gamma) ≤ nativeSetupQ1001FrameR := by
    rw [old_signed_q1_setup_frame]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hg (by norm_num))
  rw [native_source_band_mean_one]
  change (∫ ω,traceDefect (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu (n+1) ω).toFun (Annealed.sigmaBar M (n+1):ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ _
  rw [←main_completed_trace_integral_eq]
  exact main_completed_frame_return_of_ratio M (n+1) n (Annealed.sigmaBar M n)
    nativeSetupQ1001FrameR (Annealed.sigmaBar_characterization M n).1 hratio.1 (hratio.2.trans hE)

end
end ASDExplicitGamma.Native

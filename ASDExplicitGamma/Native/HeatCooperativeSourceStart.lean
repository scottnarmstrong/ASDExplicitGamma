module

public import ASDExplicitGamma.Native.HeatCooperativeSystem
public import ASDExplicitGamma.Native.GenericSourceBandInitial
public import ASDExplicitGamma.Cold.NativeTrace

/-! NATIVE_START comparison for the actual simultaneous band. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Cold
open scoped ENNReal

/-- The actual simultaneous source-band moment at time zero obeys the exact
interpolated profile used by every configured cooperative-system start row. -/
theorem nativeSourceBand_startMoment_le_profile
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height k : ℕ)
    (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeSourceBandAverage M n height
      (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x ^ (k : ℝ)) 0 ≤
      (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := cutoffTraceDefect M n n
  have htheta1 : theta M ≤ 1 := by
    rw [theta]
    exact (div_le_one₀ (by norm_num [gammaZero])).2 hgamma
  have hfirstCap : ordinaryMean M n ≤ ENNReal.ofReal (3 / 50 : ℝ) := by
    apply hstate.1.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 3 / 50) htheta1
  have hfirst : (∫⁻ ω, ‖f ω‖ₑ ∂μ) ≤ ENNReal.ofReal (3 / 50 : ℝ) := by
    have heq : ordinaryMean M n = ∫⁻ ω, ‖f ω‖ₑ ∂μ := by
      unfold ordinaryMean f μ
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg
        (Variational.cutoffTraceDefect_nonneg M n n ω)]
    rw [heq] at hfirstCap
    exact hfirstCap
  have hrootCap : root20 M n ≤ ENNReal.ofReal (21 / 100 : ℝ) := by
    apply hstate.2.2.1.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      (2013 / 10000 : ℝ) * theta M ≤ (2013 / 10000 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left htheta1 (by norm_num)
      _ ≤ 21 / 100 := by norm_num
  have h20 : eLpNorm f 20 μ ≤ ENNReal.ofReal (21 / 100 : ℝ) := by
    simpa only [root20, f, μ] using hrootCap
  have hf : AEStronglyMeasurable f μ :=
    (Variational.cutoffTraceDefect_measurable M n n).aestronglyMeasurable
  have hmoment := nativeStartMoment_integral_le hf h20 hfirst k hk1 hk20
  have hf0 (ω) : 0 ≤ f ω := Variational.cutoffTraceDefect_nonneg M n n ω
  have hfk : MemLp f k μ := by
    have hmono := (Cold.coldNativeTrace_zero_memLp hrootCap).mono_exponent
      (by exact_mod_cast hk20 : (k : ℝ≥0∞) ≤ 20)
    simpa only [Cold.coldNativeTrace, Int.natCast_zero, add_zero, f, μ] using hmono
  have hIntNorm := hfk.integrable_norm_pow (p := k) (by omega : k ≠ 0)
  have hpowInt : Integrable (fun ω => f ω ^ k) μ := by
    convert hIntNorm using 1
    ext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  have hlintegral :
      (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ) =
        ENNReal.ofReal (∫ ω, f ω ^ k ∂μ) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (f ω ^ k) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 ω), ENNReal.rpow_natCast]
        rw [← ENNReal.ofReal_pow (hf0 ω)]
      _ = ENNReal.ofReal (∫ ω, f ω ^ k ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hpowInt
          (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) k)).symm
  have hIntegral : ∫ ω, f ω ^ k ∂μ ≤
      (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
    rw [hlintegral] at hmoment
    have hnonneg : 0 ≤ ∫ ω, f ω ^ k ∂μ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) k)
    simpa only [ENNReal.toReal_ofReal hnonneg] using hmoment
  have haverage :
      nativeSourceBandAverage M n height
        (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x ^ (k : ℝ)) 0 =
        ∫ ω, f ω ^ k ∂μ := by
    unfold nativeSourceBandAverage nativeSourceBandScalar
    simp only [Real.sqrt_zero, zero_smul, add_zero]
    simp_rw [native_source_model_trace_older_eq, Real.rpow_natCast]
    simp only [f, μ]
  rw [haverage]
  exact hIntegral

end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.HeatCooperativeSourceStartW
public import ASDExplicitGamma.Native.HeatStepThetaRow
public import ASDExplicitGamma.Native.HeatCooperativeSourcePowerW

/-! Theta-scaled NATIVE_START profile: the state's `θ`-proportional mean and root caps give the
interpolated moment bound with the extra factor `θ^k`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open ASDExplicitGamma.Cold
open scoped ENNReal

variable {W : NativeAmp}

/-- Normalizing by `τ` reduces the theta-scaled start caps to the endpoint interpolation. -/
theorem nativeStartMoment_integral_theta_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {τ : ℝ} (hτ : 0 < τ)
    (h20 : eLpNorm f 20 μ ≤ ENNReal.ofReal ((21 / 100 : ℝ) * τ))
    (hfirst : ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ENNReal.ofReal ((3 / 50 : ℝ) * τ))
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ).toReal ≤
      τ ^ k * ((3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1)) := by
  have hτ0 : 0 ≤ τ := hτ.le
  let g : Ω → ℝ := τ⁻¹ • f
  have hg : AEStronglyMeasurable g μ := hf.const_smul τ⁻¹
  have hfg : f = τ • g := by
    funext ω; simp [g, hτ.ne']
  have hfactor : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.mpr hτ).ne'
  have hfirstScale : ∫⁻ ω, ‖f ω‖ₑ ∂μ = ENNReal.ofReal τ * ∫⁻ ω, ‖g ω‖ₑ ∂μ := by
    calc _ = ∫⁻ ω, ‖g ω‖ₑ * ENNReal.ofReal τ ∂μ := by
          apply lintegral_congr; intro ω
          rw [hfg, Pi.smul_apply, enorm_smul, Real.enorm_eq_ofReal hτ0, mul_comm]
      _ = (∫⁻ ω, ‖g ω‖ₑ ∂μ) * ENNReal.ofReal τ := lintegral_mul_const'' _ (hg.enorm)
      _ = _ := by rw [mul_comm]
  have hfirstN : ∫⁻ ω, ‖g ω‖ₑ ∂μ ≤ ENNReal.ofReal (3 / 50 : ℝ) := by
    apply (ENNReal.mul_le_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    calc ENNReal.ofReal τ * ∫⁻ ω, ‖g ω‖ₑ ∂μ = ∫⁻ ω, ‖f ω‖ₑ ∂μ := hfirstScale.symm
      _ ≤ ENNReal.ofReal ((3 / 50 : ℝ) * τ) := hfirst
      _ = ENNReal.ofReal τ * ENNReal.ofReal (3 / 50 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (3 / 50 : ℝ))]; ring
  have hrootScale : eLpNorm f 20 μ = ENNReal.ofReal τ * eLpNorm g 20 μ := by
    rw [hfg, eLpNorm_const_smul, Real.enorm_eq_ofReal hτ0]
  have hrootN : eLpNorm g 20 μ ≤ ENNReal.ofReal (21 / 100 : ℝ) := by
    apply (ENNReal.mul_le_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    calc ENNReal.ofReal τ * eLpNorm g 20 μ = eLpNorm f 20 μ := hrootScale.symm
      _ ≤ ENNReal.ofReal ((21 / 100 : ℝ) * τ) := h20
      _ = ENNReal.ofReal τ * ENNReal.ofReal (21 / 100 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (21 / 100 : ℝ))]; ring
  have hmoment := nativeStartMoment_integral_le hg hrootN hfirstN k hk1 hk20
  have hfin : (∫⁻ ω, ‖g ω‖ₑ ^ (k : ℝ) ∂μ) ≠ ⊤ := by
    have hb := lintegral_enorm_natPow_le_holder20_of_caps hg k hk1 hk20 hrootN hfirstN
    exact ne_top_of_le_ne_top (by finiteness) hb
  have hmomentScale : (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ) =
      ENNReal.ofReal τ ^ k * ∫⁻ ω, ‖g ω‖ₑ ^ (k : ℝ) ∂μ := by
    calc _ = ∫⁻ ω, ENNReal.ofReal τ ^ k * ‖g ω‖ₑ ^ (k : ℝ) ∂μ := by
          apply lintegral_congr; intro ω
          calc _ = (ENNReal.ofReal τ * ‖g ω‖ₑ) ^ (k : ℝ) := by
                rw [hfg, Pi.smul_apply, enorm_smul, Real.enorm_eq_ofReal hτ0]
            _ = ENNReal.ofReal τ ^ (k : ℝ) * ‖g ω‖ₑ ^ (k : ℝ) :=
                ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
            _ = _ := by rw [ENNReal.rpow_natCast]
      _ = _ := lintegral_const_mul'' _ (hg.enorm.pow_const (k : ℝ))
  rw [hmomentScale, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hτ0]
  exact mul_le_mul_of_nonneg_left hmoment (pow_nonneg hτ0 _)

/-- The actual simultaneous source-band moment at time zero obeys the exact
interpolated profile used by every configured cooperative-system start row. -/
theorem nativeSourceBand_startMoment_le_profile_theta_W
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height k : ℕ)
    (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeSourceBandAverage_W W M n height
      (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x ^ (k : ℝ)) 0 ≤
      theta M ^ k * ((3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := cutoffTraceDefect M n n
  have hθpos : 0 < theta M := by
    rw [theta]; exact div_pos M.shellPrefix.gamma_pos (by norm_num [gammaZero])
  have hfirst : (∫⁻ ω, ‖f ω‖ₑ ∂μ) ≤ ENNReal.ofReal ((3 / 50 : ℝ) * theta M) := by
    have heq : ordinaryMean M n = ∫⁻ ω, ‖f ω‖ₑ ∂μ := by
      unfold ordinaryMean f μ
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg
        (Variational.cutoffTraceDefect_nonneg M n n ω)]
    rw [← heq]
    exact hstate.1
  have hrootCap : root20 M n ≤ ENNReal.ofReal ((21 / 100 : ℝ) * theta M) := by
    apply hstate.2.2.1.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have h20 : eLpNorm f 20 μ ≤ ENNReal.ofReal ((21 / 100 : ℝ) * theta M) := by
    simpa only [root20, f, μ] using hrootCap
  have hf : AEStronglyMeasurable f μ :=
    (Variational.cutoffTraceDefect_measurable M n n).aestronglyMeasurable
  have hmoment := nativeStartMoment_integral_theta_le hf hθpos h20 hfirst k hk1 hk20
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
      theta M ^ k * ((3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1)) := by
    rw [hlintegral] at hmoment
    have hnonneg : 0 ≤ ∫ ω, f ω ^ k ∂μ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) k)
    simpa only [ENNReal.toReal_ofReal hnonneg] using hmoment
  have haverage :
      nativeSourceBandAverage_W W M n height
        (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x ^ (k : ℝ)) 0 =
        ∫ ω, f ω ^ k ∂μ := by
    unfold nativeSourceBandAverage_W nativeSourceBandScalar_W
    simp only [Real.sqrt_zero, zero_smul, add_zero]
    simp_rw [native_source_model_trace_older_eq, Real.rpow_natCast]
    simp only [f, μ]
  rw [haverage]
  exact hIntegral


/-- The actual integer-power source moments inherit the theta-scaled NATIVE_START profile. -/
theorem native_source_band_momentK_start_le_profile_theta_W
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height k : ℕ)
    (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeSourceBandMomentK_W W M n height k 0 ≤
      theta M ^ k * ((3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1)) := by
  simpa [nativeSourceBandMomentK_W] using
    nativeSourceBand_startMoment_le_profile_theta_W (W := W) M h n height k hgamma hstate hk1 hk20

end ASDExplicitGamma.Native

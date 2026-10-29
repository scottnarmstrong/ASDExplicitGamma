module

public import ASDExplicitGamma.Native.GenericSourceBandMomentDerivativeW
public import ASDExplicitGamma.Native.GenericSourceBandInitialW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The actual simultaneous source root controlled throughout heat time. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- Integrate the actual simultaneous raw moment derivative, including zero
moments and every partial time. -/
theorem native_source_band_root_raw_increment_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nativeSourceBandMoment_W W M n height t^((20:ℝ)⁻¹)-
      nativeSourceBandMoment_W W M n height 0^((20:ℝ)⁻¹) ≤
      t*nativeSourceRawMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
        (nativeSourceFullResponseCap M.gamma height) := by
  let f := nativeSourceBandMoment_W W M n height
  let c := nativeSourceRawMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
    (nativeSourceFullResponseCap M.gamma height)
  have hg0 := M.shellPrefix.gamma_pos.le
  have hc : 0 ≤ c := by
    dsimp [c,nativeSourceRawMomentIncrement,nativeSourceRawShellVarianceCap,nativeSourceFullResponseCap,
      rawTraceFullResponseCap,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128]
    positivity
  have hheat := native_source_band_moment_heat_W (W := W) M h hM n height hheight
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    hheat.1.mono (fun _ ht => ht.1)
  have hdf : ∀ τ ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (deriv f τ) τ := by
    intro τ hτ
    have hd := hheat.2 τ hτ.1
    rw [hd.deriv]
    exact hd
  have hh := raw_p20_moment_root_sub_le_integral hcont
    (fun τ _ => native_source_band_moment_nonneg_W M n height τ) hdf
    (fun _ _ => hc)
    (integrableOn_const (C := c) (by rw [Real.volume_Icc]; norm_num))
    (fun τ hτ => native_source_band_moment_derivative_raw_W M h hM hg n height hheight hpast hstate τ hτ)
    (s := 0) (t := t) (by norm_num) ht0 ht1
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hh

/-- The prime L20 seminorm is the real moment root, with finiteness supplied
by the actual bank before applying toReal. -/
theorem native_source_band_trace_L20_eq_root_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure =
      ENNReal.ofReal (nativeSourceBandMoment_W W M n height t^((20:ℝ)⁻¹)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)
  have hmem : MemLp T (ENNReal.ofReal 20) μ :=
    (native_source_band_raw_factors_W M h hM hg n height hpast t ht1).1
  have hTm : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable_W n height t)).aestronglyMeasurable
  have he : nativeSourceBandMoment_W W M n height t^((20:ℝ)⁻¹)=
      (eLpNorm T (ENNReal.ofReal 20) μ).toReal :=
    positiveLpNorm_eq_eLpNorm_toReal μ (p := 20) (by norm_num) T
      (fun _ => modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 _) hmem
  have hnorm : eLpNorm T (ENNReal.ofReal 20) μ=eLpNorm' T 20 μ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤20)] using
      eLpNorm_eq_eLpNorm' (by norm_num : ENNReal.ofReal (20:ℝ)≠0) ENNReal.ofReal_ne_top hTm
  rw [he,←hnorm,ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]

/-- The actual simultaneous source law obeys the raw generic norm cap
uniformly for all heat times in the source interval. -/
theorem native_source_band_trace_L20_raw_cap_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
      ((7/2:ℝ)*((3/50:ℝ)*theta M)+nativeSourceRawMomentIncrement height
        (nativeSourceRawShellVarianceCap M.gamma height) (nativeSourceFullResponseCap M.gamma height)) := by
  have hinc := native_source_band_root_raw_increment_W (W := W) M h hM hg n height hheight hpast hstate t ht0 ht1
  have hstart := native_source_band_initial_root_le M h n hstate
  simp only [nativeSourceBandMoment_W] at hinc
  rw [native_source_band_p20_root_zero_W] at hinc
  change nativeSourceBandMoment_W W M n height t^((20:ℝ)⁻¹)-nativeSourceBandRoot M n 0 ≤ _ at hinc
  have hg0 := M.shellPrefix.gamma_pos.le
  have hc : 0 ≤ nativeSourceRawMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
      (nativeSourceFullResponseCap M.gamma height) := by
    unfold nativeSourceRawMomentIncrement nativeSourceRawShellVarianceCap nativeSourceFullResponseCap
      rawTraceFullResponseCap nativeSourceK nativeSourceM nativeSourceQ nativeSourceB128
    positivity
  have htime := mul_le_mul_of_nonneg_right ht1 hc
  have htheta : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  rw [native_source_band_trace_L20_eq_root_W M h hM hg n height hpast t ht1]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hinc,hstart,htime,mul_nonneg (show (0:ℝ)≤87/10000 by norm_num) htheta]

end
end ASDExplicitGamma.Native

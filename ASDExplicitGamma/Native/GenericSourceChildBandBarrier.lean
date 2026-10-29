module

public import ASDExplicitGamma.Native.GenericSourceChildBandRefinedDerivative
public import ASDExplicitGamma.Inverse.SourceMomentBarrier
public import ASDExplicitGamma.Native.GenericSourceChildBandEndpoint

/-! The actual child trace seminorm and a strict p20 invariant-region comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The prime L20 seminorm is the real moment root, with finiteness supplied
by the actual bank before applying toReal. -/
theorem native_source_child_band_trace_L20_eq_root
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure =
      ENNReal.ofReal (nativeSourceChildBandMoment M n height t^((20:ℝ)⁻¹)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := fun ω => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω)
  have hmem : MemLp T (ENNReal.ofReal 20) μ :=
    (native_source_child_band_raw_factors M h hM hg n height hpast t ht1).1
  have hTm : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_child_band_scalar_measurable n height t)).aestronglyMeasurable
  have he : nativeSourceChildBandMoment M n height t^((20:ℝ)⁻¹)=
      (eLpNorm T (ENNReal.ofReal 20) μ).toReal :=
    positiveLpNorm_eq_eLpNorm_toReal μ (p := 20) (by norm_num) T
      (fun _ => modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 _) hmem
  have hnorm : eLpNorm T (ENNReal.ofReal 20) μ=eLpNorm' T 20 μ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤20)] using
      eLpNorm_eq_eLpNorm' (by norm_num : ENNReal.ofReal (20:ℝ)≠0) ENNReal.ofReal_ne_top hTm
  rw [he,←hnorm,ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]


/-- A strict scalar budget discharges the entire actual-path trace cap.
The initial norm and scalar payments are kept explicit for the numerical consumer. -/
theorem native_source_child_band_uniform_cap_of_budget
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (a c X : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hbudget : a+c<X)
    (hstart : eLpNorm' (cutoffTraceDefect M n (n-1)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal a)
    (hcost : nativeSourceChildRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
      (nativeSourceChildFullResponseCap M.gamma height) X ≤ c) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, eLpNorm'
      (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal X := by
  let f := nativeSourceChildBandMoment M n height
  let df := fun t => ∫ ω, nativeSourceChildBandPowerGenerator M h n height t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hheat := native_source_child_band_moment_heat M h hM n height hheight
  have hroot0 : 0 ≤ f 0^((20:ℝ)⁻¹) :=
    Real.rpow_nonneg (native_source_child_band_moment_nonneg M n height 0) _
  have hstart' : f 0^((20:ℝ)⁻¹) ≤ a := by
    have hzero : (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height 0 ω)) = cutoffTraceDefect M n (n-1) :=
      funext (native_source_child_band_trace_zero M n height)
    have heq := native_source_child_band_trace_L20_eq_root M h hM hg n height hpast 0 (by norm_num)
    rw [hzero] at heq
    rw [heq] at hstart
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstart
    change (ENNReal.ofReal (f 0^((20:ℝ)⁻¹))).toReal ≤ (ENNReal.ofReal a).toReal at hh
    simpa only [ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal hroot0] using hh
  have hX : 0 ≤ X := (add_nonneg ha hc).trans hbudget.le
  have hh := source_p20_moment_strict_barrier f df
    (hheat.1.mono (fun _ ht => ht.1))
    (fun t _ => native_source_child_band_moment_nonneg M n height t)
    (fun t ht => hheat.2 t ht.1) a c X ha hc hbudget hstart' ?_
  · intro t ht
    rw [native_source_child_band_trace_L20_eq_root M h hM hg n height hpast t ht.2]
    exact ENNReal.ofReal_le_ofReal (hh t ht)
  · intro t ht htx
    have htrace : eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
        modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω))
        20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal X := by
      rw [native_source_child_band_trace_L20_eq_root M h hM hg n height hpast t ht.2.le]
      exact ENNReal.ofReal_le_ofReal htx
    have hder := native_source_child_band_moment_derivative_refined M h hM hg n height hheight hpast hstate
      t ht X hX htrace
    have hd := hheat.2 t ht.1
    rw [hd.deriv] at hder
    exact hder.trans (mul_le_mul_of_nonneg_left hcost
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (native_source_child_band_moment_nonneg M n height t) _)))

end
end ASDExplicitGamma.Native

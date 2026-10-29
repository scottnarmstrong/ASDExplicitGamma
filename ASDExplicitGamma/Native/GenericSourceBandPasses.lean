module

public import ASDExplicitGamma.Native.GenericSourceBandRefinedDerivative
public import ASDExplicitGamma.Native.GenericSourceBandRoot

/-! The actual simultaneous source path through every finite refinement. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Integrate the actual simultaneous raw moment derivative, including zero
moments and every partial time. -/
theorem native_source_band_root_refined_increment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (x : ℝ) (hx : 0 ≤ x)
    (htrace : ∀ τ ∈ Set.Icc (0:ℝ) 1, eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height τ ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nativeSourceBandMoment M n height t^((20:ℝ)⁻¹)-
      nativeSourceBandMoment M n height 0^((20:ℝ)⁻¹) ≤
      t*nativeSourceRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
        (nativeSourceFullResponseCap M.gamma height) x := by
  let f := nativeSourceBandMoment M n height
  let c := nativeSourceRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
    (nativeSourceFullResponseCap M.gamma height) x
  have hg0 := M.shellPrefix.gamma_pos.le
  have hc : 0 ≤ c := by
    dsimp [c,nativeSourceRefinedMomentIncrement,nativeSourceRawShellVarianceCap,nativeSourceFullResponseCap,
      rawTraceFullResponseCap,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,
      nativeSourceInterpolationD,nativeSourceInterpolationU1,nativeSourceInterpolationU2]
    positivity
  have hheat := native_source_band_moment_heat M h hM n height hheight
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    hheat.1.mono (fun _ ht => ht.1)
  have hdf : ∀ τ ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (deriv f τ) τ := by
    intro τ hτ
    have hd := hheat.2 τ hτ.1
    rw [hd.deriv]
    exact hd
  have hh := raw_p20_moment_root_sub_le_integral hcont
    (fun τ _ => native_source_band_moment_nonneg M n height τ) hdf
    (fun _ _ => hc)
    (integrableOn_const (C := c) (by rw [Real.volume_Icc]; norm_num))
    (fun τ hτ => native_source_band_moment_derivative_refined M h hM hg n height hheight hpast hstate τ hτ
      x hx (htrace τ ⟨hτ.1.le,hτ.2.le⟩))
    (s := 0) (t := t) (by norm_num) ht0 ht1
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hh

/-- Uniform L20 cap along the simultaneous finite-band path. -/
def nativeSourceBandUniformCap (M : ABKModel 2) (n : ℤ) (height : ℕ) (x : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1,
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable n M.nu (Annealed.sigmaBar M n)
      (nativeSourceBandScalar n height t ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x

/-- One sharp refinement, keeping the starting-state reserve. -/
theorem native_source_band_uniform_cap_refine
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (x : ℝ) (hx : 0 ≤ x) (htrace : nativeSourceBandUniformCap M n height x) :
    nativeSourceBandUniformCap M n height
      ((7/2:ℝ)*((3/50:ℝ)*theta M)+nativeSourceRefinedMomentIncrement height
        (nativeSourceRawShellVarianceCap M.gamma height)
        (nativeSourceFullResponseCap M.gamma height) x) := by
  intro t ht
  have hinc := native_source_band_root_refined_increment M h hM hg n height hheight hpast hstate
    x hx htrace t ht.1 ht.2
  simp only [nativeSourceBandMoment] at hinc
  rw [native_source_band_p20_root_zero] at hinc
  change nativeSourceBandMoment M n height t^((20:ℝ)⁻¹)-nativeSourceBandRoot M n 0 ≤ _ at hinc
  have hstart := native_source_band_initial_root_le M h n hstate
  have hg0 := M.shellPrefix.gamma_pos.le
  have hc : 0 ≤ nativeSourceRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
      (nativeSourceFullResponseCap M.gamma height) x := by
    dsimp [nativeSourceRefinedMomentIncrement,nativeSourceRawShellVarianceCap,nativeSourceFullResponseCap,
      rawTraceFullResponseCap,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,
      nativeSourceInterpolationD,nativeSourceInterpolationU1,nativeSourceInterpolationU2]
    positivity
  have htime := mul_le_mul_of_nonneg_right ht.2 hc
  have htheta : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  rw [native_source_band_trace_L20_eq_root M h hM hg n height hpast t ht.2]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hinc,hstart,htime,mul_nonneg (show (0:ℝ)≤87/10000 by norm_num) htheta]

/-- Every finite source refinement pass controls the actual simultaneous laws.
The previous-cap premise of the one-pass helper is discharged by induction. -/
theorem native_source_band_generic_passes
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height pass : ℕ) (hheight : 1 ≤ height) :
    nativeSourceBandUniformCap M n height
      (nativeSourceGenericIndividualCap height ((3/50:ℝ)*theta M)
        (nativeSourceRawShellVarianceCap M.gamma height)
        (nativeSourceFullResponseCap M.gamma height) pass) := by
  let a := (3/50:ℝ)*theta M
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let f := nativeSourceFullResponseCap M.gamma height
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have ha : 0 ≤ a := mul_nonneg (by norm_num) htheta
  have he : 0 ≤ e := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp [e,nativeSourceRawShellVarianceCap]
    positivity
  have hf : 0 ≤ f := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp [f,nativeSourceFullResponseCap,rawTraceFullResponseCap]
    positivity
  change nativeSourceBandUniformCap M n height (nativeSourceGenericIndividualCap height a e f pass)
  induction pass with
  | zero =>
      intro t ht
      exact native_source_band_trace_L20_raw_cap M h hM hg n height hheight hpast hstate t ht.1 ht.2
  | succ p ih =>
      let H := nativeSourceGenericPassCap height a e f p
      let x := nativeSourceGenericIndividualCap height a e f p
      let Hnew := nativeSourceRefinedMomentIncrement height e f x
      have hx : 0 ≤ x := native_source_generic_individual_nonneg height a e f ha he hf p
      have hnew := native_source_band_uniform_cap_refine M h hM hg n height hheight hpast hstate x hx ih
      intro t ht
      change eLpNorm' _ 20 _ ≤ ENNReal.ofReal (7/2*a+min H Hnew)
      rcases le_total H Hnew with hcmp | hcmp
      · rw [min_eq_left hcmp]
        exact ih t ht
      · rw [min_eq_right hcmp]
        exact hnew t ht

/-- The literal four-pass source cap applies to the actual model laws,
without any cap, drift, bracket or bank premise on the conclusion. -/
theorem native_source_band_four_pass
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) :
    nativeSourceBandUniformCap M n height
      (nativeSourceGenericIndividualCap height ((3/50:ℝ)*theta M)
        (nativeSourceRawShellVarianceCap M.gamma height)
        (nativeSourceFullResponseCap M.gamma height) 4) :=
  native_source_band_generic_passes M h hM hg n hpast hstate height 4 hheight

end
end ASDExplicitGamma.Native

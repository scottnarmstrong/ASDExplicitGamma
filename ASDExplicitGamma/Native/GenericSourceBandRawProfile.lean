module

public import ASDExplicitGamma.Native.GenericSourceBandEfficientRoot
public import ASDExplicitGamma.Native.GenericSourceRawAllowance
public import ASDExplicitGamma.Native.GenericSourceBandFrameNorm

/-! The exact unbounded raw profile on the actual source law, using the
saved fifth of the clock rather than changing the published raw allowance. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- At every source gap h≥9, the actual endpoint trace obeys the exact raw
source-program initial allowance plus its full unbounded moment increment. -/
theorem native_source_band_trace_raw_allowance
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 9 ≤ height) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable n M.nu (Annealed.sigmaBar M n)
      (nativeSourceBandScalar n height 1 ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrameInput M.gamma (theta M) height) := by
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let f := nativeSourceFullResponseCap M.gamma height
  let H := nativeSourceRawMomentIncrement height e f
  have hinc := native_source_band_root_efficient_increment M h hM hg n height (by omega) hpast hstate
    1 (by norm_num) (by norm_num)
  simp only [one_mul,nativeSourceBandMoment] at hinc
  rw [native_source_band_p20_root_zero] at hinc
  have hcoef : nativeSourceRawMomentIncrement height ((4/5:ℝ)*e) f=(4/5:ℝ)*H := by
    dsimp [H,nativeSourceRawMomentIncrement]
    ring
  change nativeSourceBandMoment M n height 1^((20:ℝ)⁻¹)-nativeSourceBandRoot M n 0 ≤
    nativeSourceRawMomentIncrement height ((4/5:ℝ)*e) f at hinc
  rw [hcoef] at hinc
  have hstart := native_source_band_initial_root_le M h n hstate
  have hallow := native_source_raw_initial_allowance M height hheight
  rw [native_source_band_trace_L20_eq_root M h hM hg n height hpast 1 (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ nativeSourceAverageFactor*((3/50:ℝ)*theta M)+H
  change _ ≤ nativeSourceAverageFactor*((3/50:ℝ)*theta M)+H at hallow
  linarith only [hinc,hstart,hallow]

/-- The full raw frame controls the actual terminal-cutoff L20 norm at every
source gap, including arbitrarily deep tails beyond the rational E domain. -/
theorem native_source_completed_exponential_raw_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 9 ≤ height) :
    eLpNorm' (cutoffTraceDefect M (n+(height:ℤ)) n) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) height) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun ω : Cutoff.CutoffSample 2 => modelTraceObservable n M.nu (Annealed.sigmaBar M n)
    (nativeSourceBandScalar n height 1 ω)
  let g := cutoffTraceDefect M (n+(height:ℤ)) n
  let eta := nativeSourceFrameEta
  let A := 1+eta
  let C := 8*(1+1/eta)*((11/10:ℝ)*M.gamma*(height:ℝ))^2
  let R := (3:ℝ)^(2*(height:ℝ)*M.gamma)
  let x := nativeSourceExponentialRawFrameInput M.gamma (theta M) height
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hx0 : 0 ≤ x := by
    dsimp [x,nativeSourceExponentialRawFrameInput,nativeSourceExponentialRawIncrement,
      nativeSourceExponentialVarianceCap,nativeSourceExponentialFullResponseCap,
      nativeSourceRawMomentIncrement,nativeSourceAverageFactor,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128]
    positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by norm_num [A,eta,nativeSourceFrameEta]
  have hC : 0 ≤ C := by dsimp [C,eta,nativeSourceFrameEta]; positivity
  have hfm : AEStronglyMeasurable f μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable n height 1)).aestronglyMeasurable
  have hf0 (ω) : 0 ≤ f ω := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hg_nonneg (ω) : 0 ≤ g ω := cutoffTraceDefect_nonneg M (n+(height:ℤ)) n ω
  have hcap : eLpNorm' f 20 μ ≤ ENNReal.ofReal x :=
    native_source_band_trace_raw_allowance M h hM hg n hpast hstate height hheight
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M n height
  have hratioR : (Annealed.sigmaBar M (n+(height:ℤ)):ℝ)/(Annealed.sigmaBar M n:ℝ) ≤ R := by
    dsimp only [R]
    convert hratio.2 using 1
    congr 1
    ring
  have hpoint (ω) : g ω ≤ R*(A*f ω+C) := by
    have hmap := source_cutoff_pathwise_frame_map M n (n+(height:ℤ)) n ω (by omega)
      eta (by norm_num [eta,nativeSourceFrameEta])
    have hgap : ((n+(height:ℤ):ℤ):ℝ)-(n:ℝ)=(height:ℝ) := by push_cast; ring
    rw [hgap,←native_source_band_trace_one M n height ω] at hmap
    exact hmap.trans (mul_le_mul_of_nonneg_right hratioR (add_nonneg (mul_nonneg hA (hf0 ω)) hC))
  exact native_source_affine_L20_cap μ f g hfm hf0 hg_nonneg R A C x hR hA hC hx0 hcap hpoint

end
end ASDExplicitGamma.Native

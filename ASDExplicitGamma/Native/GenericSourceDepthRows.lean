module

public import ASDExplicitGamma.Native.GenericSourceSpatialAverage
public import ASDExplicitGamma.Native.GenericSourceMeanHolder
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! Actual completed source depth rows from strictly earlier native states. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Cold ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- A finite probability-space L20 cap controls the actual first moment,
with finiteness established before converting either seminorm to a real. -/
theorem native_source_mean_le_L20_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℝ) (hT : AEStronglyMeasurable T μ) (hT0 : ∀ ω, 0 ≤ T ω)
    (A : ℝ) (hA : 0 ≤ A) (hcap : eLpNorm' T 20 μ ≤ ENNReal.ofReal A) :
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ A := by
  have h2 : eLpNorm' T 2 μ ≤ ENNReal.ofReal A :=
    (eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) (by norm_num) μ hT).trans hcap
  have hone : eLpNorm' (fun _ : Ω => (1:ℝ)) 2 μ ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm'_const_of_isProbabilityMeasure 1 (by norm_num),Real.enorm_eq_ofReal (by norm_num)]
  simpa only [mul_one] using native_source_integral_product_le μ T (fun _ => 1)
    hT aestronglyMeasurable_const hT0 (fun _ => by norm_num) A 1 hA (by norm_num) h2 hone

/-- Positivity of the unbounded raw source frame on the actual parameter ray. -/
theorem native_source_actual_exponential_raw_frame_nonneg (M : ABKModel 2) (height : ℕ) :
    0 ≤ nativeSourceExponentialRawFrame M.gamma (theta M) height := by
  have hg := M.shellPrefix.gamma_pos.le
  have ht : 0 ≤ theta M := div_nonneg hg (by norm_num [gammaZero])
  dsimp [nativeSourceExponentialRawFrame,nativeSourceExponentialRawFrameInput,
    nativeSourceExponentialRawIncrement,nativeSourceExponentialVarianceCap,
    nativeSourceExponentialFullResponseCap,nativeSourceAverageFactor,nativeSourceRawMomentIncrement,
    nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,nativeSourceFrameEta]
  positivity

/-- The unbounded raw source profile controls the actual depth-d source cube
at cutoff m. Every native cutoff is at most m-9-d, strictly below m. -/
theorem native_source_depth_exponential_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) :
    eLpNorm' (cutoffTraceDefect M m (m-(depth:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (9+depth)) := by
  let height := 9+depth
  let n := m-(height:ℤ)
  have hnm : n < m := by dsimp [n,height]; omega
  have hcut : n+(height:ℤ)=m := by dsimp [n]; omega
  have hp : ∀ k < n, nativeInductionState M h k := fun k hk => hpast k (hk.trans hnm)
  have hfine := native_source_completed_exponential_raw_L20 M h hM hg n hp (hpast n hnm) height (by dsimp [height]; omega)
  rw [hcut] at hfine
  have hh : (originCube 2 (m-(depth:ℤ))).scale-((9:ℕ):ℤ)=n := by dsimp [n,height,originCube]; omega
  have hparent := native_source_parent_L20_cap M m (originCube 2 (m-(depth:ℤ))) 9
    (nativeSourceExponentialRawFrame M.gamma (theta M) height)
    (native_source_actual_exponential_raw_frame_nonneg M height)
    (by rw [hh]; exact hfine)
  exact hparent

/-- On the finite source prefix, the actual depth-d L20 row obeys the literal
piecewise four-pass/raw profile. -/
theorem native_source_depth_generic_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) (hdepth : 9+depth ≤ 1332) :
    eLpNorm' (cutoffTraceDefect M m (m-(depth:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceGenericWeakFrameProfile M.gamma (theta M) (9+depth)) := by
  let height := 9+depth
  let n := m-(height:ℤ)
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hnm : n < m := by dsimp [n,height]; omega
  have hcut : n+(height:ℤ)=m := by dsimp [n]; omega
  have hp : ∀ k < n, nativeInductionState M h k := fun k hk => hpast k (hk.trans hnm)
  unfold nativeSourceGenericWeakFrameProfile
  split_ifs with hsmall
  · have hfine := native_source_completed_generic_L20 M h hM hg n hp (hpast n hnm) height
      (by dsimp [height]; omega) hdepth
    rw [hcut] at hfine
    have hh : (originCube 2 (m-(depth:ℤ))).scale-((9:ℕ):ℤ)=n := by dsimp [n,height,originCube]; omega
    apply native_source_parent_L20_cap M m (originCube 2 (m-(depth:ℤ))) 9 _
    · exact native_source_generic_weak_frame_profile_nonneg M.gamma (theta M) (9+depth) hg0 ht0 hg hdepth
        |>.trans_eq (by rw [nativeSourceGenericWeakFrameProfile,ite_eq_left hsmall])
    · rw [hh]
      exact hfine
  · exact (native_source_depth_exponential_L20 M h hM hg m hpast depth).trans
      (ENNReal.ofReal_le_ofReal (native_source_exponential_raw_frame_le_generic M.gamma (theta M)
        (9+depth) hg0 hg ht0 hdepth))

/-- The actual source mean at each finite depth is controlled by the exact
scalar producer through 160 and the full raw profile afterwards. -/
theorem native_source_depth_generic_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) (hdepth : 9+depth ≤ 1332) :
    (∫ ω, cutoffTraceDefect M m (m-(depth:ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      nativeSourceGenericMeanProfile M.gamma (theta M) (9+depth) := by
  let height := 9+depth
  let n := m-(height:ℤ)
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hnm : n < m := by dsimp [n,height]; omega
  have hcut : n+(height:ℤ)=m := by dsimp [n]; omega
  have hp : ∀ k < n, nativeInductionState M h k := fun k hk => hpast k (hk.trans hnm)
  unfold nativeSourceGenericMeanProfile
  split_ifs with hsmall
  · have hfine := native_source_completed_generic_mean M h hM hg n hp (hpast n hnm) height
      (by dsimp [height]; omega) hdepth
    rw [hcut] at hfine
    have hsub := coldNativeCellTrace_mean_subadditive M m (originCube 2 (m-(depth:ℤ))) 9
    rw [coldNativeCellTrace_integral] at hsub
    have hh : (originCube 2 (m-(depth:ℤ))).scale-((9:ℕ):ℤ)=n := by dsimp [n,height,originCube]; omega
    rw [hh] at hsub
    exact hsub.trans hfine
  · have hcap := (native_source_depth_exponential_L20 M h hM hg m hpast depth).trans
      (ENNReal.ofReal_le_ofReal (native_source_exponential_raw_frame_le_generic M.gamma (theta M)
        (9+depth) hg0 hg ht0 hdepth))
    exact (native_source_mean_le_L20_cap (Cutoff.cutoffSampleLaw M).toMeasure _
      (cutoffTraceDefect_measurable M m (m-(depth:ℤ))).aestronglyMeasurable
      (cutoffTraceDefect_nonneg M m (m-(depth:ℤ))) _
      (native_source_generic_raw_frame_nonneg M.gamma (theta M) (9+depth) hg0 ht0 hg hdepth) hcap).2

/-- The finite mean cap directly bounds the positive extended expectation. -/
theorem native_source_depth_generic_mean_ennreal
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) (hdepth : 9+depth ≤ 1332) :
    nativeCompletedSourceMean M m depth ≤
      ENNReal.ofReal (nativeSourceGenericMeanProfile M.gamma (theta M) (9+depth)) := by
  rw [nativeCompletedSourceMean,←ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffTraceDefect M m (m-(depth:ℤ)))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-(depth:ℤ))))]
  exact ENNReal.ofReal_le_ofReal (native_source_depth_generic_mean M h hM hg m hpast depth hdepth)

/-- The unbounded raw profile bounds the positive extended source mean. -/
theorem native_source_depth_exponential_mean_ennreal
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) :
    nativeCompletedSourceMean M m depth ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (9+depth)) := by
  have hmean := native_source_mean_le_L20_cap (Cutoff.cutoffSampleLaw M).toMeasure _
    (cutoffTraceDefect_measurable M m (m-(depth:ℤ))).aestronglyMeasurable
    (cutoffTraceDefect_nonneg M m (m-(depth:ℤ))) _
    (native_source_actual_exponential_raw_frame_nonneg M (9+depth))
    (native_source_depth_exponential_L20 M h hM hg m hpast depth)
  rw [nativeCompletedSourceMean,←ofReal_integral_eq_lintegral_ofReal hmean.1
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-(depth:ℤ))))]
  exact ENNReal.ofReal_le_ofReal hmean.2

/-- The usual extended L20 seminorm obeys the finite source profile. -/
theorem native_source_depth_generic_eLpNorm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) (hdepth : 9+depth ≤ 1332) :
    eLpNorm (cutoffTraceDefect M m (m-(depth:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceGenericWeakFrameProfile M.gamma (theta M) (9+depth)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
    (cutoffTraceDefect_measurable M m (m-(depth:ℤ))).aestronglyMeasurable]
  exact native_source_depth_generic_L20 M h hM hg m hpast depth hdepth

/-- The usual extended L20 seminorm obeys the full unbounded raw profile. -/
theorem native_source_depth_exponential_eLpNorm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) :
    eLpNorm (cutoffTraceDefect M m (m-(depth:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (9+depth)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
    (cutoffTraceDefect_measurable M m (m-(depth:ℤ))).aestronglyMeasurable]
  exact native_source_depth_exponential_L20 M h hM hg m hpast depth

end
end ASDExplicitGamma.Native

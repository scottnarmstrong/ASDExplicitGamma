module

public import ASDExplicitGamma.Native.GenericSourceBandMeanPointwiseW
public import ASDExplicitGamma.Native.GenericSourceBandMomentsW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Exact actual mean heat identity and independent polynomial integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- The actual source mean generator is Bochner integrable, independently
of the differential inequality to be established. -/
theorem native_source_band_mean_generator_integrable_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t : ℝ) :
    Integrable (nativeSourceBandMeanGenerator_W W M h n height t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  unfold nativeSourceBandMeanGenerator_W
  apply integrable_finsetSum Finset.univ
  intro i _
  let b := q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))
  let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let H := pureFluxMainCubeQ3Directions n b L
  have htest := source_q3_covariance_trace_regular n b L Φ hΦ
  have hmem := native_source_band_test_memLp_W (W := W) M h hM n height hheight
    (modelCovarianceTrace Φ H) htest.1 htest.2 t 2 (by norm_num)
  have hi := (hmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (2:ℝ))).const_mul
    ((1/2:ℝ)*(nativeSourceBandCoef_W W n height i)^2)
  convert hi using 2 with ω
  ring

/-- The derivative is the literal integrable mean generator sum, in the
same true starting frame throughout the heat path. -/
theorem native_source_band_mean_heat_generator_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ContinuousOn (nativeSourceBandMean_W W M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceBandMean_W W M n height)
      (∫ ω, nativeSourceBandMeanGenerator_W W M h n height t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  have hh := native_source_band_mean_shell_heat_W (W := W) M h hM n height hheight
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
      (nativeSourceBandCoef_W W n height i)^2 * modelCovarianceTrace (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar_W W n height t ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, nativeSourceBandMeanGenerator_W W M h n height t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [Finset.mul_sum]
    rfl
  rw [he] at hd
  exact hd

end
end ASDExplicitGamma.Native

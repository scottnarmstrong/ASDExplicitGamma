module

public import ASDExplicitGamma.Native.GenericSourceChildBandHeat
public import ASDExplicitGamma.Inverse.SourceQ3TraceRegularity
public import ASDExplicitGamma.Gaussian.BandModelMoments

/-! Polynomial moments and the literal integrable generator for the refined
child-cube heat path, before any norm bound or differential comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Every polynomially bounded measurable test has all finite moments on
the actual simultaneous band, using its actual Gaussian realization. -/
theorem native_source_child_band_test_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : C(closure (cubeSet (originCube 2 (n-1))),ℝ) → ℝ)
    (hΦ : Measurable Φ) (hgrowth : HasPolynomialGrowth Φ)
    (t p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun ω : Cutoff.CutoffSample 2 => Φ (nativeSourceChildBandScalar n height t ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closure (cubeSet (originCube 2 (n-1)))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (n-1))).isCompact_closure
  let sourceChildBandMomentHeightNonzero : NeZero height := ⟨by omega⟩
  have hk : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  obtain ⟨A,v,hA,hlaw⟩ := exists_modelBand_realization K M h hM
    (nativeSourceBandIndex n height) hk
  exact memLp_bandModel_test K M ell n hK (nativeSourceBandIndex n height) hA A hlaw
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ hΦ hgrowth t hp
/-- The actual complete mean source generator at simultaneous band time `t`. -/
def nativeSourceChildBandMeanGenerator (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height, (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n))
    (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)

/-- The actual source mean generator is Bochner integrable, independently
of the differential inequality to be established. -/
theorem native_source_child_band_mean_generator_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t : ℝ) :
    Integrable (nativeSourceChildBandMeanGenerator M h n height t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Φ := modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  unfold nativeSourceChildBandMeanGenerator
  apply integrable_finsetSum Finset.univ
  intro i _
  let b := q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))
  let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let H := pureFluxMainCubeQ3Directions (n-1) b L
  have htest := source_q3_covariance_trace_regular (n-1) b L Φ hΦ
  have hmem := native_source_child_band_test_memLp M h hM n height hheight
    (modelCovarianceTrace Φ H) htest.1 htest.2 t 2 (by norm_num)
  exact (hmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (2:ℝ))).const_mul (1/2:ℝ)

/-- The derivative is the literal integrable mean generator sum, in the
same true starting frame throughout the heat path. -/
theorem native_source_child_band_mean_heat_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ContinuousOn (nativeSourceChildBandMean M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceChildBandMean M n height)
      (∫ ω, nativeSourceChildBandMeanGenerator M h n height t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  have hh := native_source_child_band_mean_shell_heat M h hM n height hheight
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
      modelCovarianceTrace (modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n))
        (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, nativeSourceChildBandMeanGenerator M h n height t ω
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

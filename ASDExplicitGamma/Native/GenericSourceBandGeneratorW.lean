module

public import ASDExplicitGamma.Native.GenericSourceBandHistoryW
public import ASDExplicitGamma.Inverse.SourceGaussianBandTrace
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The actual simultaneous-band mean derivative as the finite sum of the
sharp physical q3 shell generators. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

variable {W : NativeAmp}

/-- Actual average of a test along the simultaneous physical source band. -/
def nativeSourceBandAverage_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (Φ : C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω : Cutoff.CutoffSample 2, Φ (nativeSourceBandScalar_W W n height t ω)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The exact simultaneous-band mean heat identity uses the complete finite
sum of the canonical q3 shell covariance contractions in the same true frame. -/
theorem native_source_band_average_shell_heat_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (nativeSourceBandAverage_W W M n height Φ) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceBandAverage_W W M n height Φ)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        (nativeSourceBandCoef_W W n height i)^2 * modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar_W W n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  classical
  let sourceBandGeneratorHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet (originCube 2 n))
  let k := nativeSourceBandIndex n height
  have hk : Function.Injective k := by
    intro i j hij
    apply Fin.ext
    dsimp [k,nativeSourceBandIndex] at hij
    omega
  have hk0 (i : Fin height) : n < k i := by dsimp [k,nativeSourceBandIndex]; omega
  have hex (i : Fin height) :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM (k i-1) (K := K)
  choose T v hv hlaw using hex
  simp only [sub_add_cancel] at hlaw
  let c := nativeSourceBandCoef_W W n height
  let T' : Fin height → GaussianFactorL2 ℕ →L[ℝ] C(K,ℝ) := fun i => c i • T i
  let A := bandFactor T'
  let w := bandDirections v
  have hw : Summable (fun j => ‖w j‖^2) := bandDirections_summable v hv
  have hlawW (i : Fin height) := map_shell_smul_eq K M (k i) (hv i) (T i) (hlaw i) (c i)
  have hband := modelBandW_law_of_factors (fun _ : Fin height => GaussianFactorL2 ℕ)
    K M k c hk T' v hv hlawW
  have hband' : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBandW K k c) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hw A) := hband
  have hCov (x : C(K,ℝ)) : modelCovarianceTrace Φ (fun j => A (w j)) x =
      ∑ i : Fin height, (c i)^2 * modelCovarianceTrace Φ
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) x := by
    rw [source_gaussian_band_covariance_trace_sum v hv T' Φ hΦ.1 x]
    apply Finset.sum_congr rfl
    intro i _
    have hklabel : k i=n+((i.val+1:ℕ):ℤ) := by dsimp [k,nativeSourceBandIndex]; omega
    have hlawi : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
          (ω.1 (n+((i.val+1:ℕ):ℤ)))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i)) := by
      simpa only [hklabel] using hlaw i
    have hfun : (fun j => T' i (v i j)) = fun j => c i • T i (v i j) := rfl
    rw [hfun, modelCovarianceTrace_smul']
    rw [source_q3_test_covariance_trace_eq_of_fresh_law n M h hM (i.val+1)
      (T i) (v i) (hv i) hlawi Φ hΦ x]
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hheat := c1On_bandModelAverageW K M ell n hK k c hk0 hw A hband'
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ hΦ
  have hmean : bandModelAverageW K M n k c (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ=nativeSourceBandAverage_W W M n height Φ := rfl
  rw [hmean] at hheat
  refine ⟨hheat.1,?_⟩
  intro t ht
  have hh := hheat.2.2.1 t ht
  have hvalue : bandModelAverageW K M n k c (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ))
      (modelCovarianceTrace Φ (fun j => (ContinuousLinearMap.id ℝ C(K,ℝ)) (A (w j)))) t =
      ∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        (nativeSourceBandCoef_W W n height i)^2 * modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar_W W n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hCov _
  rw [hvalue] at hh
  exact hh

/-- Specialization of the complete shell heat identity to the actual source mean. -/
theorem native_source_band_mean_shell_heat_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ContinuousOn (nativeSourceBandMean_W W M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceBandMean_W W M n height)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        (nativeSourceBandCoef_W W n height i)^2 * modelCovarianceTrace (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
          (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar_W W n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  have hh := native_source_band_average_shell_heat_W (W := W) M h hM n height hheight
    (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
      (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1)
  have he : nativeSourceBandAverage_W W M n height
      (modelTraceObservable n M.nu (Annealed.sigmaBar M n)) = nativeSourceBandMean_W W M n height := rfl
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native

module

public import ASDExplicitGamma.Native.GenericSourceBandHeat
public import ASDExplicitGamma.Inverse.SourceGaussianBandTrace
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! Exact heat identity on the refined child observation cube. The old field
cutoff remains `n`; each fresh shell covariance is shifted by one generation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The refined source path observes the child cube while keeping the completed
old cutoff at `n` and the fixed frame at `sigmaBar M n`. -/
def nativeSourceChildBandScalar (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : C(closure (cubeSet (originCube 2 (n-1))),ℝ) :=
  olderField (closure (cubeSet (originCube 2 (n-1)))) n ω+
    Real.sqrt t • modelBand (closure (cubeSet (originCube 2 (n-1))))
      (nativeSourceBandIndex n height) ω

/-- Actual lag-one mean in its old completed true frame along fresh-band heat. -/
def nativeSourceChildBandMean (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) : ℝ :=
  ∫ ω : Cutoff.CutoffSample 2, modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    (nativeSourceChildBandScalar n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Actual average of a test along the simultaneous physical source band. -/
def nativeSourceChildBandAverage (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (Φ : C(closure (cubeSet (originCube 2 (n-1))),ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω : Cutoff.CutoffSample 2, Φ (nativeSourceChildBandScalar n height t ω)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The exact child-cube mean heat identity uses the complete finite
sum of the canonical q3 shell covariance contractions in the same true frame. -/
theorem native_source_child_band_average_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : C(closure (cubeSet (originCube 2 (n-1))),ℝ) → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (nativeSourceChildBandAverage M n height Φ) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceChildBandAverage M n height Φ)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  classical
  let sourceBandGeneratorHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet (originCube 2 (n-1)))
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
  let A := bandFactor T
  let w := bandDirections v
  have hw : Summable (fun j => ‖w j‖^2) := bandDirections_summable v hv
  have hband := modelBand_law_of_factors (fun _ : Fin height => GaussianFactorL2 ℕ)
    K M k hk T v hv hlaw
  have hband' : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hw A) := hband
  have hCov (x : C(K,ℝ)) : modelCovarianceTrace Φ (fun j => A (w j)) x =
      ∑ i : Fin height, modelCovarianceTrace Φ
        (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) x := by
    rw [source_gaussian_band_covariance_trace_sum v hv T Φ hΦ.1 x]
    apply Finset.sum_congr rfl
    intro i _
    have hklabel : k i=n+((i.val+1:ℕ):ℤ) := by dsimp [k,nativeSourceBandIndex]; omega
    have hlawi : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
          (ω.1 (n+((i.val+1:ℕ):ℤ)))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i)) := by
      simpa only [hklabel] using hlaw i
    have hlabel : n-1+((i.val+2:ℕ):ℤ)=n+((i.val+1:ℕ):ℤ) := by omega
    have hci := source_q3_test_covariance_trace_eq_of_fresh_law (n-1) M h hM (i.val+2)
      (T i) (v i) (hv i) (by simpa only [hlabel] using hlawi) Φ hΦ x
    simpa only [hlabel] using hci
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (n-1))).isCompact_closure
  have hheat := c1On_bandModelAverage K M ell n hK k hk0 hw A hband'
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ hΦ
  have hmean : bandModelAverage K M n k (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ=nativeSourceChildBandAverage M n height Φ := rfl
  rw [hmean] at hheat
  refine ⟨hheat.1,?_⟩
  intro t ht
  have hh := hheat.2.2.1 t ht
  have hvalue : bandModelAverage K M n k (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ))
      (modelCovarianceTrace Φ (fun j => (ContinuousLinearMap.id ℝ C(K,ℝ)) (A (w j)))) t =
      ∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hCov _
  rw [hvalue] at hh
  exact hh

/-- Specialization of the complete shell heat identity to the actual source mean. -/
theorem native_source_child_band_mean_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ContinuousOn (nativeSourceChildBandMean M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceChildBandMean M n height)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelCovarianceTrace (modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n))
          (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  have hh := native_source_child_band_average_shell_heat M h hM n height hheight
    (modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n))
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu
      (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1)
  have he : nativeSourceChildBandAverage M n height
      (modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)) = nativeSourceChildBandMean M n height := rfl
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native

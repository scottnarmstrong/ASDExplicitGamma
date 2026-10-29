module

public import ASDExplicitGamma.Native.GenericSourceBandHeat
public import ASDExplicitGamma.Inverse.SourceGaussianBandTrace
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! The actual simultaneous-band mean derivative as the finite sum of the
sharp physical q3 shell generators. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The actual same finite band, observed on an independently chosen square. -/
def parentBoundaryObserverBandScalar (q n : ℤ) (height : ℕ) (t : ℝ)
    (omega : Cutoff.CutoffSample 2) : C(closure (cubeSet (originCube 2 q)),ℝ) :=
  olderField (closure (cubeSet (originCube 2 q))) n omega+
    Real.sqrt t • modelBand (closure (cubeSet (originCube 2 q))) (nativeSourceBandIndex n height) omega

/-- Actual average of a test along the simultaneous physical source band. -/
def parentBoundaryObserverBandAverage (M : ABKModel 2) (q n : ℤ) (height : ℕ)
    (Φ : C(closure (cubeSet (originCube 2 q)),ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω : Cutoff.CutoffSample 2, Φ (parentBoundaryObserverBandScalar q n height t ω)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The exact simultaneous-band mean heat identity uses the complete finite
sum of the canonical q3 shell covariance contractions in the same true frame. -/
theorem parent_boundary_observer_band_average_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (q n : ℤ) (hqn : q≤n) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : C(closure (cubeSet (originCube 2 q)),ℝ) → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (parentBoundaryObserverBandAverage M q n height Φ) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (parentBoundaryObserverBandAverage M q n height Φ)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (parentBoundaryObserverBandScalar q n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  classical
  let sourceBandGeneratorHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet (originCube 2 q))
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
        (pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
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
    let s : ℕ := (n-q).toNat+i.val+1
    have hsq : q+(s:ℤ)=n+((i.val+1:ℕ):ℤ) := by
      dsimp only [s]
      push_cast
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hqn)]
      omega
    have hlaws : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun omega : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (omega.1 (q+(s:ℤ))))=
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i)) := by
      rw [hsq]
      exact hlawi
    have hh := source_q3_test_covariance_trace_eq_of_fresh_law q M h hM s
      (T i) (v i) (hv i) hlaws Φ hΦ x
    simpa only [hsq] using hh
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hheat := c1On_bandModelAverage K M ell n hK k hk0 hw A hband'
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ hΦ
  have hmean : bandModelAverage K M n k (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ=parentBoundaryObserverBandAverage M q n height Φ := rfl
  rw [hmean] at hheat
  refine ⟨hheat.1,?_⟩
  intro t ht
  have hh := hheat.2.2.1 t ht
  have hvalue : bandModelAverage K M n k (ContinuousLinearMap.id ℝ C(K,ℝ))
      (ContinuousLinearMap.id ℝ C(K,ℝ))
      (modelCovarianceTrace Φ (fun j => (ContinuousLinearMap.id ℝ C(K,ℝ)) (A (w j)))) t =
      ∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelCovarianceTrace Φ
          (pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (parentBoundaryObserverBandScalar q n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hCov _
  rw [hvalue] at hh
  exact hh


end
end ASDExplicitGamma.Native

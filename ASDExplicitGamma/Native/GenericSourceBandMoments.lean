module

public import ASDExplicitGamma.Native.GenericSourceBandPointwise
public import ASDExplicitGamma.Inverse.SourceQ3TraceRegularity
public import ASDExplicitGamma.Gaussian.BandModelMoments

/-! Actual simultaneous-band polynomial integrability, before any norm cap
or differential inequality is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Every polynomially bounded measurable test has all finite moments on
the actual simultaneous band, using its actual Gaussian realization. -/
theorem native_source_band_test_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ)
    (hΦ : Measurable Φ) (hgrowth : HasPolynomialGrowth Φ)
    (t p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun ω : Cutoff.CutoffSample 2 => Φ (nativeSourceBandScalar n height t ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  obtain ⟨A,v,hA,hlaw,_,_⟩ := native_source_band_mean_heat M h hM n height hheight
  exact memLp_bandModel_test K M ell n hK (nativeSourceBandIndex n height) hA A hlaw
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Φ hΦ hgrowth t hp

/-- The literal finite p20 generator sum is Bochner integrable on the actual
source law. Its heat integral therefore cannot conceal a missing moment. -/
theorem native_source_band_power_generator_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t : ℝ) :
    Integrable (nativeSourceBandPowerGenerator M h n height t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hΦ0 := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
  have hpower := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0 (by norm_num : (2:ℝ)≤20)
  unfold nativeSourceBandPowerGenerator
  apply integrable_finsetSum Finset.univ
  intro i _
  let b := q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))
  let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let H := pureFluxMainCubeQ3Directions n b L
  have htest := source_q3_covariance_trace_regular n b L (fun x => Φ x^(20:ℝ)) hpower
  have hmem := native_source_band_test_memLp M h hM n height hheight
    (modelCovarianceTrace (fun x => Φ x^(20:ℝ)) H) htest.1 htest.2 t 2 (by norm_num)
  have hi := hmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (2:ℝ))
  have he : (fun ω : Cutoff.CutoffSample 2 => modelPowerHeatGenerator Φ H 20
      (nativeSourceBandScalar n height t ω)) =
      (fun ω => (1/2:ℝ)*modelCovarianceTrace (fun x => Φ x^(20:ℝ)) H
        (nativeSourceBandScalar n height t ω)) := by
    funext ω
    exact (source_q3_covariance_power_identity n M.nu (Annealed.sigmaBar M n) b M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 L _).symm
  rw [he]
  exact hi.const_mul (1/2:ℝ)

end
end ASDExplicitGamma.Native
